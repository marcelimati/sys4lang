(* Copyright (C) 2024 kichikuou <KichikuouChrome@gmail.com>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, see <http://gnu.org/licenses/>.
 *)

open Common
open Base
open Jaf

let make_stmt node = { node; delete_vars = []; loc = dummy_location }

let array_alloc_stmt (v : variable) =
  let var = make_expr (Ident (v.name, UnresolvedIdent)) in
  let func = make_expr (Member (var, "Alloc", UnresolvedMember)) in
  let call =
    make_expr
      (Call
         ( func,
           List.map ~f:Option.some v.array_dim,
           BuiltinCall Bytecode.ArrayAlloc ))
  in
  make_stmt (Expression call)

class visitor ctx =
  object (self)
    inherit ivisitor ctx as _super
    val mutable initializer_funcs : declaration list = []
    val mutable global_init_stmts : statement list = []

    method insert_array_initializer_call (fdecl : fundecl) =
      (* insert `2();` at the beginning of constructor body *)
      let func = make_expr (Ident ("2", UnresolvedIdent)) in
      let call = make_expr (Call (func, [], UnresolvedCall)) in
      fdecl.body <-
        Some (make_stmt (Expression call) :: Option.value_exn fdecl.body)

    method visit_struct_decl s =
      let initialize_stmts = ref [] in
      let has_ctor = ref false in
      let needs_synth_ctor_v12 = ref false in
      (* Original Rance10 generates @0 for ANY class with properties,
         even when their backings are primitive (e.g. [MoviePlayInfo]
         has only [bool { get; set; }] properties). @0 zero-initializes
         each property backing field. [expand_struct_decls] runs
         before this visitor, so PropertyDecl is already lowered to
         MemberDecl with [<Name>]-shaped backing field names. Detect
         those (excluding compiler-injected [<vtable>] / [<void>]). *)
      let is_property_backing (v : variable) =
        let n = String.length v.name in
        n >= 3
        && Char.equal v.name.[0] '<'
        && Char.equal v.name.[n - 1] '>'
        && not (String.equal v.name "<vtable>")
        && not (String.equal v.name "<void>")
      in
      let property_name_of_backing (v : variable) =
        if is_property_backing v then
          Some (String.sub v.name ~pos:1 ~len:(String.length v.name - 2))
        else None
      in
      let ctor_bodies =
        let local =
          List.filter_map s.decls ~f:(function
            | Constructor f when Option.is_some f.body -> f.body
            | _ -> None)
        in
        let key = s.name ^ "@0" in
        let registered =
          let primary = Hashtbl.find ctx.functions key |> Option.to_list in
          let overloads =
            Hashtbl.find ctx.overloads key |> Option.value ~default:[]
          in
          primary @ overloads
          |> List.filter_map ~f:(fun f -> f.body)
        in
        if List.is_empty registered then local else registered
      in
      let ctor_count = List.length ctor_bodies in
      let ctor_assigned_properties = Hashtbl.create (module String) in
      let note_ctor_assign name =
        Hashtbl.update ctor_assigned_properties name ~f:(function
          | None -> 1
          | Some n -> n + 1)
      in
      let member_name_of_this (e : expression) =
        match e.node with
        | Member ({ node = This; _ }, name, _) ->
            if
              String.length name >= 3
              && Char.equal name.[0] '<'
              && Char.equal name.[String.length name - 1] '>'
            then Some (String.sub name ~pos:1 ~len:(String.length name - 2))
            else Some name
        | _ -> None
      in
      let rec scan_expr (e : expression) =
        match e.node with
        | Assign (EqAssign, lhs, rhs) ->
            Option.iter (member_name_of_this lhs) ~f:note_ctor_assign;
            scan_expr lhs;
            scan_expr rhs
        | Assign (_, lhs, rhs) | Binary (_, lhs, rhs) | Seq (lhs, rhs)
        | NullCoalesce (lhs, rhs) | Subscript (lhs, rhs) ->
            scan_expr lhs;
            scan_expr rhs
        | Unary (_, e) | Cast (_, e) | DummyRef (_, e) | RvalueRef e
        | OptionalMember (e, _, _) | Member (e, _, _) ->
            scan_expr e
        | Ternary (a, b, c) ->
            scan_expr a;
            scan_expr b;
            scan_expr c
        | Call (f, args, _) ->
            scan_expr f;
            List.iter args ~f:(Option.iter ~f:scan_expr)
        | NewCall (_, args) -> List.iter args ~f:(Option.iter ~f:scan_expr)
        | ArrayLiteral elems -> List.iter elems ~f:scan_expr
        | Lambda _ -> ()
        | ConstInt _ | ConstFloat _ | ConstChar _ | ConstString _ | Ident _
        | FuncAddr _ | MemberAddr _ | New _ | This | Null ->
            ()
      in
      let rec scan_stmt (stmt : statement) =
        match stmt.node with
        | Expression e | Return (Some e) | Jumps e | Case e -> scan_expr e
        | Compound stmts | Switch (_, stmts) -> List.iter stmts ~f:scan_stmt
        | If (test, cons, alt) ->
            scan_expr test;
            scan_stmt cons;
            scan_stmt alt
        | While (test, body) | DoWhile (test, body) ->
            scan_expr test;
            scan_stmt body
        | For (init, test, inc, body) ->
            scan_stmt init;
            Option.iter test ~f:scan_expr;
            Option.iter inc ~f:scan_expr;
            scan_stmt body
        | ForEach (_, _, _, arr, body) ->
            scan_expr arr;
            scan_stmt body
        | RefAssign (a, b) | ObjSwap (a, b) ->
            scan_expr a;
            scan_expr b
        | Declarations ds ->
            List.iter ds.vars ~f:(fun v -> Option.iter v.initval ~f:scan_expr)
        | Return None | EmptyStatement | Label _ | Goto _ | Continue | Break
        | Default | Jump _ | Message _ ->
            ()
      in
      List.iter ctor_bodies ~f:(List.iter ~f:scan_stmt);
      let ctor_always_assigns_property name =
        ctor_count > 0
        &&
        match Hashtbl.find ctor_assigned_properties name with
        | Some n -> n >= ctor_count
        | None -> false
      in
      let has_property =
        List.exists s.decls ~f:(function
          | MemberDecl ds -> List.exists ds.vars ~f:is_property_backing
          | _ -> false)
      in
      let v12 = Ain.version_gte ctx.ain (12, 0) in
      (* v12: interface-implementing classes need an @0 even without
         user-supplied initialization, because emit_interface_vtable_init
         runs at constructor entry to populate the <vtable> array. The
         classes show up in original Rance10's FUNC table with @0 entries
         (e.g. AchieveIcon@0, CommonFrame@0, QuestMapFrame@0); without
         synth, our build lacks these functions and any interface
         dispatch through them deref's a NULL vtable. *)
      let needs_vtable_init =
        v12 && s.is_class && not (List.is_empty s.interfaces)
      in
      if needs_vtable_init then needs_synth_ctor_v12 := true;
      if
        v12
        && List.mem
             [ "CASTimerManager"; "CompletedTrophy" ]
             s.name ~equal:String.equal
      then needs_synth_ctor_v12 := true;
      let rec is_interface_type (ty : jaf_type) =
        match ty with
        | Unresolved name | Struct (name, _) ->
            Hashtbl.mem ctx.interface_names name
        | Ref inner -> is_interface_type inner
        | _ -> false
      in
      let rec zero_for_type (ty : jaf_type) =
        match ty with
        | _ when is_interface_type ty -> None
        | Int | Bool | Float -> None
        | String -> Some (make_expr (ConstString ""))
        | Struct _ -> None
        | Ref (Struct _) -> Some (make_expr Null)
        | Ref inner -> zero_for_type inner
        | _ -> None
      in
      let backing_init_stmt (v : variable) =
        let int n = make_expr (ConstInt n) in
        let member_expr name =
          make_expr (Member (make_expr This, name, UnresolvedMember))
        in
        let type_spec ty = { ty; location = dummy_location } in
        let make_var name kind ty initval =
          {
            name;
            location = dummy_location;
            array_dim = [];
            is_const = false;
            is_private = false;
            kind;
            type_spec = type_spec ty;
            initval;
            index = None;
          }
        in
        let ident name = make_expr (Ident (name, UnresolvedIdent)) in
        let call_expr func args =
          make_expr (Call (func, List.map args ~f:Option.some, UnresolvedCall))
        in
        let method_call_expr obj name args =
          call_expr (make_expr (Member (obj, name, UnresolvedMember))) args
        in
        let add_expr lhs rhs = make_expr (Binary (Plus, lhs, rhs)) in
        let cuser_component_activity_params_init () =
          if
            not
              (v12
              && String.equal s.name "activity::detail::CUserComponentActivity"
              && String.equal v.name "<Params>")
          then None
          else
            let class_index =
              (Ain.get_struct ctx.ain s.name |> Option.value_exn).index
            in
            let lambda_short_name =
              "<lambda : activity::detail::CUserComponentActivity@2()(30, 76)>"
            in
            let lambda_full_name = s.name ^ "@" ^ lambda_short_name in
            let lambda_index =
              match Ain.get_function ctx.ain lambda_full_name with
              | Some f -> f.index
              | None ->
                  (Ain.add_function ~nr_args:1 ctx.ain lambda_full_name).index
            in
            let lambda_param = make_var "_0" Parameter String None in
            let lambda_body =
              [
                make_stmt
                  (Expression
                     (method_call_expr (make_expr This) "Create" []));
              ]
            in
            let lambda_fdecl =
              {
                name = lambda_short_name;
                loc = dummy_location;
                return = type_spec Void;
                params = [ lambda_param ];
                body = Some lambda_body;
                is_label = false;
                is_lambda = true;
                is_private = false;
                index = Some lambda_index;
                class_name = Some s.name;
                class_index = Some class_index;
              }
            in
            Hashtbl.set ctx.functions ~key:lambda_full_name ~data:lambda_fdecl;
            initializer_funcs <- Function lambda_fdecl :: initializer_funcs;
            let param_ty = Struct ("IUserComponentParam", 15) in
            let tmp =
              make_var "<dummy : new array<ref IUserComponentParam>>" LocalVar
                (Array param_ty) None
            in
            let tmp_expr = ident tmp.name in
            let tmp_decl =
              make_stmt
                (Declarations
                   {
                     decl_loc = dummy_location;
                     is_const_decls = false;
                     typespec = type_spec (Array param_ty);
                     vars = [ tmp ];
                   })
            in
            let lambda_method =
              make_expr
                (Member (make_expr This, lambda_short_name, UnresolvedMember))
            in
            let make_param =
              call_expr
                (ident "AFL_Activity_CreateUserComponentStringParam")
                [
                  make_expr
                    (ConstString
                       "\227\130\162\227\130\175\227\131\134\227\130\163\227\131\147\227\131\134\227\130\163\227\131\149\227\130\161\227\130\164\227\131\171\229\144\141");
                  lambda_method;
                ]
            in
            let pushback =
              make_stmt
                (Expression
                   (method_call_expr tmp_expr "PushBack" [ make_param ]))
            in
            let assign =
              make_stmt
                (Expression
                   (make_expr
                      (Assign
                         (EqAssign, member_expr v.name, ident tmp.name))))
            in
            Some [ tmp_decl; pushback; assign ]
        in
        let backing_array_free_stmt () =
          let func =
            make_expr (Member (member_expr v.name, "Free", UnresolvedMember))
          in
          let call = make_expr (Call (func, [], UnresolvedCall)) in
          make_stmt (Expression call)
        in
        let new_call name args =
          match Ain.get_struct ctx.ain name with
          | None -> None
          | Some s ->
              Some
                (make_expr
                   (NewCall
                      ( { ty = Struct (name, s.index); location = dummy_location },
                        List.map args ~f:(fun e -> Some e) )))
        in
        let known_v12_backing_init () =
          if not v12 then None
          else
            match (s.name, property_name_of_backing v) with
            | "QuestMapSelectionButton", Some "IsEnable" -> Some (int 1)
            | "PartyCard", Some "IsShadowMode"
            | "AegisEffectView", Some "IsHide"
            | "BadConditionView", Some "IsHide"
            | "PageButton", Some "IsSelected"
            | "GameConfig", Some "IsAskNetworkConnection"
            | "GameConfig", Some "SortType"
            | "GameOmakePlayInfo", Some "IsShowNunuharaFirstEvent"
            | "MoviePlayInfo", Some "IsPlayedChapter1BadEnd"
            | "MoviePlayInfo", Some "IsPlayedChapter1NormalEnd"
            | "MoviePlayInfo", Some "IsPlayedChapter2End"
            | "MoviePlayInfo", Some "IsPlayedOpening"
            | "PlayerCommonParam", Some "IsUsedHannyZippo"
            | "ReplayFlag", Some "IsActive"
            | "PartyChangeRound", Some "IsChanged"
            | "AegisEffectGroup", Some "IsBlockInfo"
            | "PartyBonus", Some "IsUse"
            | "PartyBonus", Some "IsFixed"
            | "InstantTimer", Some "IsEnd" ->
                Some (int 0)
            | "SimpleBattleParty", Some "EffectElementType" -> Some (int (-1))
            | "parts::detail::CPartsTimeLine", Some "HeaderWidth" ->
                Some (int 100)
            | "parts::detail::CPartsTimeLine", Some "RulerHeight" ->
                Some (int 20)
            | "parts::detail::CPartsTimeLine", Some "GridSize"
            | "parts::detail::CPartsTimeLineItem", Some "GridSize" ->
                new_call "CASSize" [ int 16; int 20 ]
            | "parts::detail::CPartsTimeLine", Some "CursorColor" ->
                new_call "CASColor" [ int 255; int 70; int 70; int 128 ]
            | "parts::detail::CPartsTimeLine", Some "RulerBaseColor"
            | "parts::detail::CPartsTimeLineItem", Some "BaseColor"
            | "parts::detail::CPartsTimeLineItem", Some "GridBaseColor" ->
                new_call "CASColor" [ int 70; int 70; int 70; int 255 ]
            | "parts::detail::CPartsTimeLine", Some "RulerDivisionColor"
            | "parts::detail::CPartsTimeLineItem", Some "GridDivisionColor" ->
                new_call "CASColor" [ int 125; int 125; int 125; int 255 ]
            | "parts::detail::CPartsTimeLine", Some "RulerTextColor" ->
                new_call "CASColor" [ int 224; int 224; int 224; int 255 ]
            | "parts::detail::CPartsTimeLine", Some "FrameNumber" ->
                Some (int 0)
            | "parts::detail::CPartsTimeLine", Some "MaxFrameNumber" ->
                Some (int 10)
            | "parts::detail::CPartsTimeLineItem", Some "SelectedColor" ->
                new_call "CASColor" [ int 120; int 120; int 180; int 255 ]
            | "parts::detail::CPartsTimeLineItem", Some "IsExpanded" ->
                Some (int 1)
            | "parts::detail::CPartsTimeLineItem", Some "IsSelected" ->
                Some (int 0)
            | "activityeditor::detail::CInstanceItem", Some "Name" ->
                Some (make_expr (ConstString ""))
            | "activity::detail::CUserComponentStringParam", Some "Name" ->
                Some (make_expr (ConstString ""))
            | "activityeditor::detail::CInstanceItem", Some "IsActive"
            | "activityeditor::detail::CInstanceItem", Some "LockEdit" ->
                Some (int 0)
            | "activityeditor::detail::CInstanceItem", Some "ShowEditor" ->
                Some (int 1)
            | "SimpleBattleSkillEffect", Some "SkillName"
            | "SimpleBattleSkillEffect", Some "CardId" ->
                Some (make_expr (ConstString ""))
            | "SimpleBattleSkillEffect", Some "SkillId"
            | "SimpleBattleSkillEffect", Some "EffectType" ->
                Some (int (-1))
            | "ClearPointBonus", Some "IsUse"
            | "SkillApCost", Some "State"
            | "AvoidanceCalculator", Some "IsSpecialEffect" ->
                Some (int 0)
            | "ElementCount", Some "ElementId"
            | "OrganizationCount", Some "OrganizationId"
            | "HastleResult", Some "PartyIndex"
            | "CASClick", Some "KeyCode" ->
                Some (int (-1))
            | "PlayerAction", Some "Type" -> Some (int 0)
            | "GameYear", Some "YearTitle" ->
                Some (make_expr (ConstString "ＸＸ"))
            | "GameYear", Some "Year" | "GameYear", Some "Month"
            | "GameYear", Some "Half" ->
                Some (int (-1))
            | "elkeditor::detail::CToolBar", Some "AxisXUsable"
            | "elkeditor::detail::CToolBar", Some "AxisYUsable"
            | "elkeditor::detail::CToolBar", Some "AxisZUsable" ->
                Some (int 1)
            | "Character", Some "Exp"
            | "Character", Some "IsFinishAttack" ->
                Some (int 0)
            | "Character", Some "NextExp" ->
                Some (int 100)
            | "stageeditor::detail::CLightArrowInstance",
              Some "IsShownScatteringLine"
            | "stageeditor::detail::CLightArrowInstance",
              Some "IsShownHemisphereLine"
            | "stageeditor::detail::CLightArrowInstance",
              Some "IsShownShadowLine" ->
                Some (int 0)
            | "RouteIndex", Some "Id" | "RouteIndex", Some "Index" ->
                Some (int (-1))
            | "QuestMapRoute", Some "X" | "QuestMapRoute", Some "Y" ->
                Some (int (-1))
            | "QuestMapPosition", Some "X" | "QuestMapPosition", Some "Y" ->
                Some (int 0)
            | "SceneStack", Some "LayerPartsNumber"
            | "SceneStack", Some "IsFinish" ->
                Some (int 0)
            | "sealtool::detail::CMapWire", Some "NumofLine" ->
                Some (int 40)
            | "sealtool::detail::CMapWire", Some "LineSpace" ->
                Some (make_expr (ConstFloat 0.5))
            | "sealtool::detail::CCamera", Some "OrthographicMag" ->
                Some (make_expr (ConstFloat 0.25))
            | ( "sealtool::detail::CCamera",
                Some "DecideViewportWidthByViewWidthMode" ) ->
                Some (int 0)
            | ( "stageeditor::detail::CCameraPanel",
                Some "EX_CAMERA_FILEPATH" ) ->
                Some
                  (add_expr
                     (call_expr (ident "SYS_AddPunct")
                        [
                          method_call_expr (ident "system") "GetSaveFolderName"
                            [];
                        ])
                     (make_expr
                        (ConstString "..\\StageEditor\\カメラ設定.txtex")))
            | "advengine::detail::CADVEngine", Some key -> (
                let key_code =
                  match key with
                  | "F2" -> Some 113
                  | "F3" -> Some 114
                  | "F4" -> Some 115
                  | "F5" -> Some 116
                  | "F6" -> Some 117
                  | "F7" -> Some 118
                  | "F8" -> Some 119
                  | "Enter" -> Some 13
                  | "Esc" -> Some 27
                  | "RClick" -> Some 2
                  | _ -> None
                in
                Option.bind key_code ~f:(fun code ->
                    new_call "CASClick" [ int code; int 1 ]))
            | _ -> None
        in
        match cuser_component_activity_params_init () with
        | Some stmts -> Some stmts
        | None ->
            let rhs =
              match known_v12_backing_init () with
              | Some rhs -> Some rhs
              | None -> (
                  match v.type_spec.ty with
                  | Array _ | Ref (Array _) -> None
                  (* Value-struct backings: the VM auto-constructs value
                     struct members when the parent page is created (their
                     @0/@2 chain runs), and the original compiler emits NO
                     @0 code for them — an explicit [new T] here allocated
                     a second object over the auto-created one at every
                     instantiation (leak + identity churn; BattleContext@0
                     carried ten of these vs original's none). *)
                  | Struct _ when not (is_interface_type v.type_spec.ty) ->
                      None
                  | _ -> zero_for_type v.type_spec.ty)
            in
            (match rhs with
            | None -> (
                match v.type_spec.ty with
                | Array _ | Ref (Array _) -> Some [ backing_array_free_stmt () ]
                | _ -> None)
            | Some rhs ->
                let target = member_expr v.name in
                let assign = make_expr (Assign (EqAssign, target, rhs)) in
                Some [ make_stmt (Expression assign) ])
      in
      List.iter s.decls ~f:(function
        | MemberDecl ds ->
            List.iter ds.vars ~f:(function
              | { array_dim = _ :: _; is_const = false; _ } as m ->
                  initialize_stmts := array_alloc_stmt m :: !initialize_stmts
              | { is_const = true; _ } -> ()
              | v ->
                  (* v12: all member types auto-initialize when a struct
                     is instantiated. The only members that need @0 are:
                     - explicit initvals ([= value] in source)
                     - property backings (explicit reset to default)
                     - multi-dim array_dim (handled by the array_dim branch
                       above as array_alloc_stmt)
                     - <vtable> field for interface-implementing classes
                       (an Array with array_dim, also handled above)
                     non_primitive used to fire @0 for any Struct/Array/etc.
                     member but original Rance10 doesn't emit @0 for
                     classes like Activity, Admiral, AddedArmyView whose
                     members are just plain Struct/Array/String. *)
                  let _ = v in
                  let non_primitive = false in
                  (match v.initval with
                  | Some init ->
                      needs_synth_ctor_v12 := true;
                      initialize_stmts :=
                        List.rev_append
                          (Declarations.make_member_init_stmts v init)
                          !initialize_stmts
                  | None ->
                      let known_v12_backing_with_ctor =
                        match (s.name, property_name_of_backing v) with
                        | ( "activity::detail::CUserComponentActivity",
                            Some "Params" )
                        | "parts::detail::CPartsTimeLine", Some "HeaderWidth"
                        | "parts::detail::CPartsTimeLine", Some "RulerHeight"
                        | "parts::detail::CPartsTimeLine", Some "GridSize"
                        | "parts::detail::CPartsTimeLine", Some "CursorColor"
                        | ( "parts::detail::CPartsTimeLine",
                            Some "RulerBaseColor" )
                        | ( "parts::detail::CPartsTimeLine",
                            Some "RulerDivisionColor" )
                        | "parts::detail::CPartsTimeLine", Some "RulerTextColor"
                        | "parts::detail::CPartsTimeLine", Some "FrameNumber"
                        | ( "parts::detail::CPartsTimeLine",
                            Some "MaxFrameNumber" )
                        | "parts::detail::CPartsTimeLineItem", Some "GridSize"
                        | "parts::detail::CPartsTimeLineItem", Some "BaseColor"
                        | ( "parts::detail::CPartsTimeLineItem",
                            Some "SelectedColor" )
                        | ( "parts::detail::CPartsTimeLineItem",
                            Some "GridBaseColor" )
                        | ( "parts::detail::CPartsTimeLineItem",
                            Some "GridDivisionColor" )
                        | "parts::detail::CPartsTimeLineItem", Some "IsExpanded"
                        | "parts::detail::CPartsTimeLineItem", Some "IsSelected"
                        | "activityeditor::detail::CInstanceItem", Some "Name"
                        | ( "activity::detail::CUserComponentStringParam",
                            Some "Name" )
                        | ( "activityeditor::detail::CInstanceItem",
                            Some "IsActive" )
                        | ( "activityeditor::detail::CInstanceItem",
                            Some "LockEdit" )
                        | ( "activityeditor::detail::CInstanceItem",
                            Some "ShowEditor" )
                        | "SimpleBattleSkillEffect", Some "SkillName"
                        | "SimpleBattleSkillEffect", Some "CardId"
                        | "SimpleBattleSkillEffect", Some "SkillId"
                        | "SimpleBattleSkillEffect", Some "EffectType"
                        | "ClearPointBonus", Some "IsUse"
                        | "SkillApCost", Some "State"
                        | "AvoidanceCalculator", Some "IsSpecialEffect"
                        | "ElementCount", Some "ElementId"
                        | "OrganizationCount", Some "OrganizationId"
                        | "HastleResult", Some "PartyIndex"
                        | "CASClick", Some "KeyCode"
                        | "PlayerAction", Some "Type"
                        | "GameYear", Some "YearTitle"
                        | "GameYear", Some "Year"
                        | "GameYear", Some "Month"
                        | "GameYear", Some "Half"
                        | "elkeditor::detail::CToolBar", Some "AxisXUsable"
                        | "elkeditor::detail::CToolBar", Some "AxisYUsable"
                        | "elkeditor::detail::CToolBar", Some "AxisZUsable"
                        | "Character", Some "Exp"
                        | "Character", Some "NextExp"
                        | "Character", Some "IsFinishAttack"
                        | ( "stageeditor::detail::CLightArrowInstance",
                            Some "IsShownScatteringLine" )
                        | ( "stageeditor::detail::CLightArrowInstance",
                            Some "IsShownHemisphereLine" )
                        | ( "stageeditor::detail::CLightArrowInstance",
                            Some "IsShownShadowLine" )
                        | "RouteIndex", Some "Id"
                        | "RouteIndex", Some "Index"
                        | "QuestMapRoute", Some "X"
                        | "QuestMapRoute", Some "Y"
                        | "QuestMapPosition", Some "X"
                        | "QuestMapPosition", Some "Y"
                        | "SceneStack", Some "LayerPartsNumber"
                        | "SceneStack", Some "IsFinish"
                        | "sealtool::detail::CMapWire", Some "NumofLine"
                        | "sealtool::detail::CMapWire", Some "LineSpace"
                        | "sealtool::detail::CCamera", Some "OrthographicMag"
                        | ( "sealtool::detail::CCamera",
                            Some "DecideViewportWidthByViewWidthMode" )
                        | ( "stageeditor::detail::CCameraPanel",
                            Some "EX_CAMERA_FILEPATH" )
                          ->
                            true
                        | _ -> false
                      in
                      if
                        v12 && is_property_backing v
                        && (ctor_count = 0 || known_v12_backing_with_ctor)
                      then (
                        (* v12 @0 zero-initializes each property backing
                           field — including strings ([S_PUSH ""]) and
                           refs ([PUSH -1]) since the original emits init
                           for those too. Takes precedence over non_primitive.
                           Delegate/FuncType backings have no zero literal
                           ([zero_for_type] returns None) and auto-init,
                           so don't trigger @0 for those. *)
                        match property_name_of_backing v with
                        | Some name
                          when ctor_always_assigns_property name
                               && not known_v12_backing_with_ctor ->
                            ()
                        | _ -> (
                            match backing_init_stmt v with
                            | Some stmts ->
                                needs_synth_ctor_v12 := true;
                                initialize_stmts :=
                                  List.rev_append stmts !initialize_stmts
                            | None -> ()))
                      else if non_primitive then needs_synth_ctor_v12 := true))
        | Constructor fdecl ->
            has_ctor := true;
            if Option.is_some fdecl.body then
              self#insert_array_initializer_call fdecl
        | _ -> ());
      let _ = has_property in
      (* Removed [if has_property then needs_synth_ctor_v12 := true]:
         that blanket over-emitted @0 for 286 classes whose property
         backings either don't exist (computed properties) or don't
         need zero-init. needs_synth_ctor_v12 now only fires when a
         backing actually contributes an init statement (handled in
         the loop above) or when a member is non-primitive. *)
      if (not (List.is_empty !initialize_stmts)) || !has_ctor
         || (v12 && !needs_synth_ctor_v12) then (
        (* generate array initializer for the class *)
        let name = if !has_ctor then "2" else "0" in
        let full_name = s.name ^ "@" ^ name in
        let skip_v12_synth_ctor =
          v12 && not !has_ctor
          &&
          Set.mem
            (Set.of_list
               (module String)
               [
                 "AssistantButton@0";
                 "AssistantSelector@0";
                 "BadCondition@0";
                 "BattleInsertion@0";
                 "BattleSceneSetSimple@0";
                 "CASColorF@0";
                 "CharacterEventCollection@0";
                 "Enemy@0";
                 "GetCardInformation@0";
                 "LevelUpResult@0";
                 "OmakePlayInfo@0";
                 "Quest@0";
                 "QuestMapObject@0";
                 "QuestMapReadInfo@0";
                 "QuestMapRouteInfo@0";
                 "QuestMapSelection@0";
                 "SaveObjectInfo@0";
                 "SeekButton@0";
                 "SimpleBattlePartyBonus@0";
                 "ThumbnailButtonCollection@0";
                 "activityeditor::detail::CAEProjectForm@0";
                 "activityeditor::detail::CActivityData@0";
                 "elkeditor::detail::CCommonSetting@0";
               ])
            full_name
        in
        if not skip_v12_synth_ctor then (
        (* v11 [declarations.ml] pre-registers [Class@2] before
           allocating the matching [Class@0] constructor slot, so it
           interleaves with the constructor in the function table.
           Reuse that pre-registered slot if present; fall back to
           appending a new entry otherwise (pre-v11 / no constructor). *)
        let f_index =
          match Ain.get_function ctx.ain full_name with
          | Some f -> f.index
          | None -> (Ain.add_function ctx.ain full_name).index
        in
        let fdecl =
          {
            name;
            loc = dummy_location;
            return = { ty = Void; location = dummy_location };
            params = [];
            body = Some (List.rev !initialize_stmts);
            is_label = false;
            is_lambda = false;
            is_private = false;
            index = Some f_index;
            class_name = Some s.name;
            class_index =
              Some (Ain.get_struct ctx.ain s.name |> Option.value_exn).index;
          }
        in
        Hashtbl.add_exn ctx.functions ~key:full_name ~data:fdecl;
        initializer_funcs <- Function fdecl :: initializer_funcs;
        if not !has_ctor then
          (* register the generated constructor in ain *)
          let ain_s = Option.value_exn (Ain.get_struct ctx.ain s.name) in
          Ain.write_struct ctx.ain { ain_s with constructor = f_index })
      )

    method! visit_declaration decl =
      let v12 = Ain.version_gte ctx.ain (12, 0) in
      (* v12 dropped the GSET (global initvals) section. Globals with a
         source initializer now need their init emitted as bytecode in
         the global-init function [name "0"]. Globals without initvals
         are left to the VM's default global-page initialization. *)
      let visit_global v =
        if v.is_const then ()
        else
          let has_array_dim = not (List.is_empty v.array_dim) in
          if has_array_dim then
            global_init_stmts <- array_alloc_stmt v :: global_init_stmts
          else if v12 then
            match v.initval with
            | None -> ()
            | Some init ->
                let target =
                  make_expr (Ident (v.name, UnresolvedIdent))
                in
                let assign =
                  make_expr (Assign (EqAssign, target, init))
                in
                global_init_stmts <-
                  make_stmt (Expression assign) :: global_init_stmts
      in
      match decl with
      | Global ds -> List.iter ds.vars ~f:visit_global
      | GlobalGroup { vardecls = dss; _ } ->
          List.iter dss ~f:(function ds -> List.iter ds.vars ~f:visit_global)
      | StructDef s -> self#visit_struct_decl s
      | Function fdecl when is_constructor fdecl ->
          self#insert_array_initializer_call fdecl
      | _ -> ()

    method generate_initializers () =
      let null_func =
        Function
          {
            name = "NULL";
            loc = dummy_location;
            return = { ty = Void; location = dummy_location };
            params = [];
            body = Some [];
            is_label = false;
            is_lambda = false;
            is_private = false;
            index = Some 0;
            class_name = None;
            class_index = None;
          }
      in
      let funcs = List.rev (null_func :: initializer_funcs) in
      if List.is_empty global_init_stmts then funcs
      else
        let global_init =
          Function
            {
              name = "0";
              loc = dummy_location;
              return = { ty = Void; location = dummy_location };
              params = [];
              body = Some (List.rev global_init_stmts);
              is_label = false;
              is_lambda = false;
              is_private = false;
              index = Some (Ain.add_function ctx.ain "0").index;
              class_name = None;
              class_index = None;
            }
        in
        global_init :: funcs
  end
