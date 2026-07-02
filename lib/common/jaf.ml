(* Copyright (C) 2021 Nunuhara Cabbage <nunuhara@haniwa.technology>
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

open Base
open Printf

type location = Lexing.position * Lexing.position

let dummy_location = (Lexing.dummy_pos, Lexing.dummy_pos)

type unary_op =
  | UPlus
  | UMinus
  | LogNot
  | BitNot
  | PreInc
  | PreDec
  | PostInc
  | PostDec
  (* v11 foreach increment/decrement on the loop counter — emitted by
     foreach desugaring. Behaves like PreInc/PreDec for codegen. *)
  | ForeachInc
  | ForeachDec

type binary_op =
  | Plus
  | Minus
  | Times
  | Divide
  | Modulo
  | Equal
  | NEqual
  | RefEqual
  | RefNEqual
  | LT
  | GT
  | LTE
  | GTE
  | LogOr
  | LogAnd
  | BitOr
  | BitXor
  | BitAnd
  | LShift
  | RShift

type assign_op =
  | EqAssign
  | PlusAssign
  | MinusAssign
  | TimesAssign
  | DivideAssign
  | ModuloAssign
  | OrAssign
  | XorAssign
  | AndAssign
  | LShiftAssign
  | RShiftAssign
  | CharAssign

type jaf_type =
  | Untyped
  | Unresolved of string
  | Void
  | Int
  | LongInt
  | Bool
  | Float
  | String
  | Struct of string * int
  | Enum of string * int
  | Ref of jaf_type
  | Array of jaf_type
  | Wrap of jaf_type
  | HLLParam
  | HLLFunc
  | HLLFunc2
  | Delegate of (string * int) option
  | FuncType of (string * int) option
  | IMainSystem
  | NullType
  | TyFunction of function_type
  | TyMethod of function_type
  | MemberPtr of string * jaf_type
  | TypeUnion of jaf_type * jaf_type

and function_type = jaf_type list * jaf_type

let jaf_type_equal (a : jaf_type) b = Poly.equal a b

let ft_compatible (args, ret) (args', ret') =
  jaf_type_equal ret ret'
  && List.length args = List.length args'
  && List.for_all2_exn args args' ~f:jaf_type_equal

(* Overload identity: two methods overload each other only if their
   parameter types differ. Return type is not part of the signature
   (C-like / Java-like rule). If parameters are identical, the two
   decls are "the same method" — one is either a prototype, the body,
   or an actual duplicate. *)
let params_compatible a b =
  List.length a = List.length b
  && List.for_all2_exn a b ~f:jaf_type_equal

let is_scalar = function
  | Int | Bool | Float | LongInt | Enum _ | FuncType _ -> true
  | _ -> false

let is_ref_scalar = function
  | Ref (Int | Bool | Float | LongInt | Enum _ | FuncType _) -> true
  | _ -> false

let rec array_base_and_rank = function
  | Array t ->
      let b, r = array_base_and_rank t in
      (b, r + 1)
  | b -> (b, 0)

let array_rank t = snd (array_base_and_rank t)

type type_specifier = { mutable ty : jaf_type; location : location }

type ident_type =
  | UnresolvedIdent
  | LocalVariable of int * location
  (* v11 lambda capture: [index] in the enclosing scope's local frame,
     [level] hops upward (1 = direct parent, 2 = grandparent, …). *)
  | CapturedVariable of int * int
  | GlobalVariable of int
  | GlobalConstant
  | FunctionName of string
  | HLLName
  | System
  | BuiltinFunction of Bytecode.builtin

type member_type =
  | UnresolvedMember
  | ClassVariable of int
  | ClassConst of string
  | ClassMethod of string * int
  (* v11 property access. Type analysis rewrites reads into a call
     to the getter and assignments into a call to the setter, so
     later passes never encounter this variant. *)
  | ClassProperty of {
      prop_class : string;
      prop_name : string;
      prop_getter_index : int option;
      prop_setter_index : int option;
    }
  (* v11 user-bodied event access. When a class declares
     [event T Name;] but its [<Name>] backing field has been elided
     because the user supplied [Name::add] / [Name::remove] bodies at
     top level, [obj.Name += h] / [obj.Name -= h] no longer routes
     through a delegate-typed member — type analysis rewrites the
     [Assign] into a call through the user's [Name::add] /
     [Name::remove] method instead. *)
  | ClassEvent of {
      event_class : string;
      event_name : string;
      event_add_index : int option;
      event_remove_index : int option;
    }
  | HLLFunction of string * string
  | SystemFunction of Bytecode.syscall
  | BuiltinMethod of Bytecode.builtin
  | BuiltinHLL of string

type variable_type = Parameter | LocalVar | GlobalVar | ClassVar

type call_type =
  | UnresolvedCall
  | FunctionCall of int
  | MethodCall of int * int
  | HLLCall of int * int
  | SystemCall of Bytecode.syscall
  | BuiltinCall of Bytecode.builtin
  | FuncTypeCall of int
  | DelegateCall of int

type expression = {
  mutable ty : jaf_type;
  mutable node : ast_expression;
  loc : location;
}

and ast_expression =
  | ConstInt of int
  | ConstFloat of float
  | ConstChar of string
  | ConstString of string
  | Ident of string * ident_type
  | FuncAddr of string * int option
  | MemberAddr of string * string * int
  | Unary of unary_op * expression
  | Binary of binary_op * expression * expression
  | Assign of assign_op * expression * expression
  | Seq of expression * expression
  | Ternary of expression * expression * expression
  (* v11 optional member access [a?.b]: evaluate [a]; if non-NULL
     produce its [.b] member, else short-circuit to NULL. Resolved
     in type analysis much like [Member]. *)
  | OptionalMember of expression * string * member_type
  (* v11 null-coalesce [a ?? b]: evaluate [a]; if NULL evaluate [b]
     and return that, else return [a]. Both sides must produce a
     compatible type. *)
  | NullCoalesce of expression * expression
  | Cast of jaf_type * expression
  | Subscript of expression * expression
  | Member of expression * string * member_type
  | Call of expression * expression option list * call_type
  | New of type_specifier
  (* v12 constructor call with arguments: `new T(a, b, c)`. The plain
     [New] node still represents the parameterless form (`new T` and
     `new T()`). Type analysis types this as [Ref T] like plain [New]
     and resolves the constructor based on the argument types. *)
  | NewCall of type_specifier * expression option list
  (* v12 array literal `[e1, e2, ...]`. Carries the element expressions
     in source order. The literal's resulting type is `Array elem_ty` where
     `elem_ty` is the common type of the elements (computed during type
     analysis). Used in initializer position (`array@int x = [1, 2];`)
     and as a regular expression value (`f([1, 2, 3])`). *)
  | ArrayLiteral of expression list
  | DummyRef of int * expression
  | RvalueRef of expression
  | This
  | Null
  | Lambda of fundecl

and statement = {
  mutable node : ast_statement;
  mutable delete_vars : int list;
  loc : location;
}

and ast_statement =
  | EmptyStatement
  | Declarations of vardecls
  | Expression of expression
  | Compound of statement list
  | Label of string
  | If of expression * statement * statement
  | While of expression * statement
  | DoWhile of expression * statement
  | For of statement * expression option * expression option * statement
  (* v11 foreach: [foreach (var : array)] or [foreach_r] for reverse,
     with optional explicit index variable name as the third field.
     Lowered into a while loop by [desugar_foreach] before type
     analysis runs, so codegen never sees this variant directly. *)
  | ForEach of bool * string * string option * expression * statement
  | Goto of string
  | Continue
  | Break
  | Switch of expression * statement list
  | Case of expression
  | Default
  | Return of expression option
  | Jump of string
  | Jumps of expression
  | Message of string
  | RefAssign of expression * expression
  | ObjSwap of expression * expression

and variable = {
  name : string;
  location : location;
  array_dim : expression list;
  is_const : bool;
  mutable is_private : bool;
  kind : variable_type;
  type_spec : type_specifier;
  initval : expression option;
  mutable index : int option;
}

and vardecls = {
  decl_loc : location;
  is_const_decls : bool;
  typespec : type_specifier;
  vars : variable list;
}

and fundecl = {
  mutable name : string;
  loc : location;
  return : type_specifier;
  mutable params : variable list;
  mutable body : statement list option;
  is_label : bool;
  is_lambda : bool;
  mutable is_private : bool;
  mutable index : int option;
  mutable class_name : string option;
  mutable class_index : int option;
}

let make_expr ?(ty = Untyped) ?(loc = dummy_location) node = { ty; node; loc }
let clone_expr (e : expression) = { e with loc = e.loc }

let ft_of_fundecl fundecl =
  let args = List.map fundecl.params ~f:(fun p -> p.type_spec.ty) in
  let ret = fundecl.return.ty in
  (args, ret)

let is_constructor (f : fundecl) =
  match f.class_name with
  | Some s -> String.equal f.name (snd (Util.parse_qualified_name s))
  | _ -> false

let mangled_name fdecl =
  match fdecl.class_name with
  | Some s ->
      (* v12 namespace function shape: if [fdecl.name] already begins
         with [class_name::] (e.g. ["ActivityUserObject::CreateObjectFromName"]
         when class_name = "ActivityUserObject"), the function is a
         top-level [Class::Method] definition where [Method] isn't
         declared in [Class]'s body. Original Rance10 keeps the [::]
         form in the FUNC table strings. Keep [fdecl.name] as-is
         rather than re-mangling to [Class@Method]. [class_name] is
         still set so the body's [this] resolves.

         Excludes the [Bar::get] / [Bar::set] property-accessor shape
         which uses bare [::] in the name but lives in a class body
         and SHOULD mangle to [Class@Bar::get]. *)
      let prefix = s ^ "::" in
      if String.is_prefix fdecl.name ~prefix then
        fdecl.name
      else
        s
        ^
        let _, s = Util.parse_qualified_name s in
        if String.equal fdecl.name s then "@0"
        else if String.equal fdecl.name ("~" ^ s) then "@1"
        else "@" ^ fdecl.name
  | None -> fdecl.name

type access_specifier = Public | Private

(* v11 property declaration inside a class body: `T Name { get; set; }`.
   Expanded at declaration-analysis time into a mangled backing field
   `<Name>` plus synthetic get/set methods, matching what the original
   v11 compiler emits. [pd_accessors] lists the accessor names in
   source order, validated at expansion time (only `get`/`set` are
   legal). *)
type property_decl = {
  pd_loc : location;
  pd_typespec : type_specifier;
  pd_name : string;
  pd_accessors : (string * location) list;
  (* v11+ property initializer (`float Rate { get; set; } = 1.0;`).
     Lowered into the synthesized backing field's [initval] so the
     class's auto-generated `@0` ctor emits the assignment. *)
  pd_initval : expression option;
}

(* v11 event declaration inside a class body: `event T Name;`. Expanded
   at declaration-analysis time into a delegate-typed mangled backing
   field `<Name>` plus prototype-only [Name::add(T value)] and
   [Name::remove(T value)] methods (kept body-less; the original compiler
   emits matching function-table entries that the runtime never invokes
   for auto-events — [+= h] / [-= h] dispatch lowers to direct delegate
   ops on the [<Name>] field). *)
type event_decl = {
  ed_loc : location;
  ed_typespec : type_specifier;
  ed_name : string;
}

type struct_declaration =
  | AccessSpecifier of access_specifier
  | MemberDecl of vardecls
  | Constructor of fundecl
  | Destructor of fundecl
  | Method of fundecl
  | PropertyDecl of property_decl
  | EventDecl of event_decl

type structdecl = {
  name : string;
  is_class : bool;
  loc : location;
  (* v11+ interface list from `class Foo implements I1, I2 {`. Empty for
     plain classes/structs. Not yet wired through to the .ain interface
     table — populated by the parser, ignored by current codegen. *)
  interfaces : string list;
  mutable decls : struct_declaration list;
}

type enumdecl = {
  name : string option;
  loc : location;
  values : (string * expression option) list;
}

type global_group = { name : string; loc : location; vardecls : vardecls list }

type declaration =
  | Function of fundecl
  | Global of vardecls
  | GlobalGroup of global_group
  | FuncTypeDef of fundecl
  | DelegateDef of fundecl
  | StructDef of structdecl
  | Enum of enumdecl

type ast_node =
  | ASTExpression of expression
  | ASTStatement of statement
  | ASTVariable of variable
  | ASTDeclaration of declaration
  | ASTStructDecl of struct_declaration
  | ASTType of type_specifier

let ast_node_pos = function
  | ASTExpression e -> e.loc
  | ASTStatement s -> s.loc
  | ASTVariable v -> v.location
  | ASTDeclaration d -> (
      match d with
      | Function f -> f.loc
      | Global d -> d.decl_loc
      | GlobalGroup gg -> gg.loc
      | FuncTypeDef f -> f.loc
      | DelegateDef f -> f.loc
      | StructDef s -> s.loc
      | Enum e -> e.loc)
  | ASTStructDecl d -> (
      match d with
      | AccessSpecifier _ -> dummy_location
      | MemberDecl d -> d.decl_loc
      | Constructor f -> f.loc
      | Destructor f -> f.loc
      | Method f -> f.loc
      | PropertyDecl p -> p.pd_loc
      | EventDecl e -> e.ed_loc)
  | ASTType t -> t.location

(* v11 property metadata recorded on a class during declaration
   analysis: each property has a type, an optional getter method,
   and an optional setter method (each declared as `Name::get` /
   `Name::set` in the function table). Use sites `obj.Name`
   dispatch through the methods. See [Declarations.expand_property_decl]
   for the lowering from [PropertyDecl]. *)
type property_info = {
  (* Reference to the mutable [type_specifier] from the original
     [PropertyDecl] so later type-resolution passes (which mutate
     the type_specifier in place to turn [Unresolved] into [Struct _]
     etc.) are reflected here too. *)
  prop_typespec : type_specifier;
  prop_getter : fundecl option;
  prop_setter : fundecl option;
}

(* Helper for callers that just want the resolved type. *)
let prop_info_ty (p : property_info) = p.prop_typespec.ty

type jaf_struct = {
  name : string;
  loc : location;
  index : int;
  members : (string, variable) Hashtbl.t;
  properties : (string, property_info) Hashtbl.t;
}

let new_jaf_struct name loc index =
  {
    name;
    loc;
    index;
    members = Hashtbl.create (module String);
    properties = Hashtbl.create (module String);
  }

(* HLL libraries can declare multiple functions with the same name but
   different parameter signatures (v11). The first-seen declaration is
   stored in [functions] under its plain name; any same-name declaration
   with distinct parameter types appends to [overloads] so call-site
   resolution can pick by argument types. Empty [overloads] for non-v11
   libraries. *)
type library = {
  hll_name : string;
  functions : (string, fundecl) Hashtbl.t;
  overloads : (string, fundecl list) Hashtbl.t;
}

type context = {
  ain : Ain.t;
  version : int; (* ain_major_version * 100 + ain_minor_version *)
  globals : (string, variable) Hashtbl.t;
  structs : (string, jaf_struct) Hashtbl.t;
  functions : (string, fundecl) Hashtbl.t;
  (* v11 overloaded methods / functions, keyed by [mangled_name]
     ([Class@Name] for methods, plain function name otherwise). The
     entry in [functions] holds the first-seen declaration; any
     overload with distinct parameter types is appended here. Resolved
     at call sites by matching against the actual argument types. Empty
     for pre-v11 programs. *)
  overloads : (string, fundecl list) Hashtbl.t;
  functypes : (string, fundecl) Hashtbl.t;
  delegates : (string, fundecl) Hashtbl.t;
  libraries : (string, library) Hashtbl.t;
  (* v11 property / event accessor names whose body the user supplies
     at top level (as [T Class::Name { get { body } set { body } }] or
     [event T Class::Name { add { body } remove { body } }]).
     Populated by a pre-scan over all parsed jaf files. Keys take the
     [Class@Name::accessor] mangled shape. Used by [expand_property_decl]
     to elide auto-stub bodies / backing fields when the user owns
     accessor dispatch, and by the StructDef define check to skip the
     "no definition found" diagnostic for the prototype emitted by the
     auto-expansion. *)
  user_bodied_accessors : (string, unit) Hashtbl.t;
  (* v12 property backing-field gating: keys are `Class@PropName` for
     properties whose top-level user-bodied accessor body references
     [this.<PropName>]. expand_property_decl uses this to decide
     whether to emit the [<PropName>] backing field. Original v12
     elides the field when no accessor uses it (e.g. computed
     getters like [int Count { get { return this.m_data.Numof(); } }]
     — emitting it anyway shifts member offsets and causes the VM
     to access-violate on struct access at load. *)
  properties_with_backing_ref : (string, unit) Hashtbl.t;
  (* v12 auto-property accessors are declared in classes.jaf but
     original Rance10 places their FUNC slots next to the first real
     method body for that class. These tables carry the delayed slots
     across per-file declaration visitors. *)
  v12_pending_property_stubs : (string, fundecl list) Hashtbl.t;
  v12_property_stub_classes_emitted : (string, unit) Hashtbl.t;
  v12_property_getter_dup_indices : (int, int list) Hashtbl.t;
  v12_class_interfaces : (string, string list) Hashtbl.t;
  v12_struct_methods : (string, fundecl list) Hashtbl.t;
  v12_body_dup_indices : (int, int list) Hashtbl.t;
  v12_pending_lambdas : fundecl Queue.t;
  v12_current_body_group : string option ref;
  v12_current_body_file_no : int option ref;
  v12_pending_interface_proto_groups : string Queue.t;
  v12_pending_interface_proto_seen : (string, unit) Hashtbl.t;
  v12_allocated_interface_proto_groups : (string, unit) Hashtbl.t;
  v12_structs_with_member_initvals : (string, unit) Hashtbl.t;
  (* v12 decompiled sources often spell struct-valued properties as
     [ref T Prop { ... }] because the getter returns a ref to the backing
     storage. Original storage is still a value struct unless user code
     treats the property as nullable (optional access, NULL assignment or
     NULL comparison). Keys are [Class@PropName]. *)
  nullable_ref_properties : (string, unit) Hashtbl.t;
  (* Pre-scanned constructor metadata for source structs/classes. Used by
     v12 property lowering before type registration has seen every target
     declaration. *)
  structs_with_constructor : (string, unit) Hashtbl.t;
  structs_with_default_constructor : (string, unit) Hashtbl.t;
  (* v12 enum constants. Keys are qualified `EnumName::ValueName`;
     values are the assigned int. Resolved at call sites the same
     way as globals — the resolved expression is rewritten to a
     ConstInt during type analysis. Empty for projects with no
     enum declarations. *)
  enum_values : (string, int) Hashtbl.t;
  (* Set of registered enum type names. Type-resolution treats
     names found here as Int (the underlying storage class). *)
  enum_types : (string, unit) Hashtbl.t;
  (* v11+ interface type names (declared via `interface Name { ... }`
     rather than `class Name { ... }`). The .ain binary distinguishes
     interface refs from struct refs via separate data_type codes
     (89 = IFace vs 13 = Struct). Populated when register_type_
     declarations sees a StructDef with [is_class = false]. *)
  interface_names : (string, unit) Hashtbl.t;
  (* v12: classes that [implements] one or more interfaces are also
     encoded with dt=89 (IFace) when referenced as a variable/param/
     member, despite being declared as [class]. Original Rance10
     example: [parts::detail::CUserComponentParts p] (a class
     implementing IUserComponentParts) encodes as dt=89 iface(332).
     Plain classes without implements stay as dt=21 Ref(Struct). *)
  iface_compatible_classes : (string, unit) Hashtbl.t;
  (* Pre-scanned set of delegate-type names (just the names, registered
     before [DelegateDef] visitors run). Used by expand_struct_decls
     member reordering to detect delegate-typed members when the
     delegate's full registration happens after the struct's. *)
  delegate_names : (string, unit) Hashtbl.t;
  v12_reference_array_delegates : (string, fundecl) Hashtbl.t option;
  v12_reference_delegate_order : string list;
  v12_reference_delegate_cursor : int ref;
  (* v11+ interface inheritance: source jaf for v12 lists all
     inherited methods inline because decomp can't distinguish them.
     E.g. [interface IButtonParts] declares all 207 IParts methods +
     its own 31. Original Rance10 only registers the 31 own ones;
     inherited stay under IParts.

     [interface_parent.{I} = Parent] if I "inherits" from Parent,
     detected by method-set overlap (>=90% of Parent's methods are
     in I and Parent has >=50 methods). Lookup [I.AddColor] falls
     back to [Parent.AddColor] when registration is filtered. *)
  interface_parent : (string, string) Hashtbl.t;
  (* Set of [Interface@MethodName] that have been filtered as
     inherited. Used by callsite resolution to redirect lookups to
     the parent interface. *)
  interface_inherited_methods : (string, (string, unit) Hashtbl.t) Hashtbl.t;
}

let find_hll_function ctx lib func =
  match Hashtbl.find ctx.libraries lib with
  | Some l -> Hashtbl.find l.functions func
  | None -> None

type resolved_name =
  | ResolvedLocal of variable
  | ResolvedGlobal of variable
  | ResolvedFunction of fundecl
  | ResolvedMember of jaf_struct * variable
  | ResolvedMethod of jaf_struct * fundecl
  | ResolvedLibrary of library
  | ResolvedSystem
  | ResolvedBuiltin of Bytecode.builtin
  (* v12 enum constant resolved as an int value. Type analysis
     rewrites the source Ident to ConstInt so codegen treats it
     as any other integer literal. *)
  | ResolvedEnumValue of int
  (* v12 user-type cast: `StructName(arg)` is treated as a cast to
     the struct type. The Call handler in type analysis rewrites
     this into a [Cast (Struct (name, idx), arg)] node. *)
  | ResolvedStructType of string * int
  | UnresolvedName

class environment ctx current_function =
  object (self)
    val mutable stack = []

    val mutable variables =
      match current_function with Some f -> f.params | None -> []

    method push = stack <- variables :: stack

    method pop =
      match stack with
      | [] -> failwith "visitor tried to pop root environment"
      | prev :: rest ->
          variables <- prev;
          stack <- rest

    method push_var decl = variables <- decl :: variables

    method var_list =
      List.append variables (List.fold stack ~init:[] ~f:List.append)

    method current_function = current_function

    method current_class =
      match current_function with
      | Some { class_name = Some name; class_index = Some index; _ } ->
          Some (Struct (name, index))
      | _ -> None

    method get_local name =
      List.find variables ~f:(fun v -> String.equal v.name name)

    method resolve name =
      (* v12 enum stringifiers and similar `Receiver@member` functions
         (e.g. `EKeyType@String`) surface as `Receiver::member` in
         source. The strtab keeps the `@` form, so when a qualified
         lookup misses, try swapping the last `::` for `@` before
         giving up. Mirror change in [decompiler/codeGen.ml]'s
         [pr_callable Function _]. Uses the depth-aware split so
         templated names like `Class::Method<Ns::Type>` swap the
         outer `::` between Class and Method, not the inner one
         inside the template args. *)
      let try_at_swap_lookup tbl =
        match Util.last_toplevel_double_colon name with
        | Some i ->
            let left = String.sub name ~pos:0 ~len:i in
            let right =
              String.sub name ~pos:(i + 2) ~len:(String.length name - i - 2)
            in
            Hashtbl.find tbl (left ^ "@" ^ right)
        | None -> None
      in
      let ctx_resolve ctx =
        match Hashtbl.find ctx.globals name with
        | Some g -> ResolvedGlobal g
        | None -> (
            (* Check enum values BEFORE the @-swap function lookup —
               otherwise `EnumName::ValueName` would resolve to the
               synthesized `EnumName@String` stringifier instead of
               the enum's `ValueName`. *)
            match Hashtbl.find ctx.enum_values name with
            | Some v -> ResolvedEnumValue v
            | None -> (
                match Hashtbl.find ctx.functions name with
                | Some f -> ResolvedFunction f
                | None -> (
                    match try_at_swap_lookup ctx.functions with
                    | Some f -> ResolvedFunction f
                    | None -> (
                        match Hashtbl.find ctx.libraries name with
                        | Some l -> ResolvedLibrary l
                        | None -> (
                            (* v12 user-type cast: bare struct name in
                               expression position is a cast target;
                               the Call handler turns it into a Cast. *)
                            match Hashtbl.find ctx.structs name with
                            | Some s -> ResolvedStructType (name, s.index)
                            | None -> UnresolvedName)))))
      in
      match name with
      | "system" ->
          (* v11 ships a [system] HLL library that overlaps with the
             classic [system.*] syscall receiver. If the library is
             registered, prefer it — otherwise the [Output] et al.
             HLL entries get shadowed and calls emit [CALLSYS] instead
             of [CALLHLL], which the v11 VM rejects. *)
          (match Hashtbl.find ctx.libraries name with
          | Some l -> ResolvedLibrary l
          | None -> ResolvedSystem)
      | "assert" ->
          ResolvedBuiltin
            (Option.value_exn (Bytecode.builtin_function_of_string "assert"))
      | _ -> (
          match self#get_local name with
          | Some v -> ResolvedLocal v
          | None -> (
              match self#current_class with
              | Some (Struct (s_name, _)) -> (
                  let s = Hashtbl.find_exn ctx.structs s_name in
                  match Hashtbl.find s.members name with
                  | Some v -> ResolvedMember (s, v)
                  | None -> (
                      match
                        Hashtbl.find ctx.functions (s_name ^ "@" ^ name)
                      with
                      | Some f -> ResolvedMethod (s, f)
                      | None -> ctx_resolve ctx))
              | _ -> ctx_resolve ctx))

    method resolve_qualified sname name =
      match Hashtbl.find ctx.structs sname with
      | None -> UnresolvedName
      | Some s -> (
          match Hashtbl.find s.members name with
          | Some v -> ResolvedMember (s, v)
          | None -> UnresolvedName)
  end

class ivisitor ctx =
  object (self)
    val env_stack = Stack.singleton (new environment ctx None)
    val mutable current_struct_name : string option = None
    method env = Stack.top_exn env_stack
    method env_stack = env_stack
    method current_struct_name = current_struct_name

    method visit_expression (e : expression) =
      match e.node with
      | ConstInt _ -> ()
      | ConstFloat _ -> ()
      | ConstChar _ -> ()
      | ConstString _ -> ()
      | Ident _ -> ()
      | FuncAddr _ -> ()
      | MemberAddr _ -> ()
      | Unary (_, e) -> self#visit_expression e
      | Binary (_, lhs, rhs) ->
          self#visit_expression lhs;
          self#visit_expression rhs
      | Assign (_, lhs, rhs) ->
          self#visit_expression lhs;
          self#visit_expression rhs
      | Seq (a, b) ->
          self#visit_expression a;
          self#visit_expression b
      | Ternary (a, b, c) ->
          self#visit_expression a;
          self#visit_expression b;
          self#visit_expression c
      | OptionalMember (obj, _, _) -> self#visit_expression obj
      | NullCoalesce (a, b) ->
          self#visit_expression a;
          self#visit_expression b
      | Cast (_, obj) -> self#visit_expression obj
      | Subscript (arr, i) ->
          self#visit_expression arr;
          self#visit_expression i
      | Member (obj, _, _) -> self#visit_expression obj
      | Call (f, args, _) ->
          self#visit_expression f;
          List.iter args ~f:(Option.iter ~f:self#visit_expression)
      | New t -> self#visit_type_specifier t
      | NewCall (t, args) ->
          self#visit_type_specifier t;
          List.iter args ~f:(Option.iter ~f:self#visit_expression)
      | ArrayLiteral elems -> List.iter elems ~f:self#visit_expression
      | DummyRef (_, e) -> self#visit_expression e
      | RvalueRef e -> self#visit_expression e
      | This -> ()
      | Null -> ()
      | Lambda f -> self#visit_fundecl f

    method visit_vardecls (ds : vardecls) =
      self#visit_type_specifier ds.typespec;
      List.iter ds.vars ~f:(fun v ->
          (match v.kind with LocalVar -> self#env#push_var v | _ -> ());
          self#visit_variable v)

    method visit_statement (s : statement) =
      match s.node with
      | EmptyStatement -> ()
      | Declarations ds -> self#visit_vardecls ds
      | Expression e -> self#visit_expression e
      | Compound stmts ->
          (* v12 declares variables in one if branch and uses them in
             a sibling branch (e.g. `if (...) { ref T x = ...; }
             else { x <- ...; } x.method();` ). Lifting all Compound
             declarations into the enclosing scope matches v12
             semantics — push/pop would lose the binding when the
             other branch needs it. *)
          List.iter stmts ~f:self#visit_statement
      | Label _ -> ()
      | If (test, cons, alt) ->
          self#visit_expression test;
          self#visit_statement cons;
          self#visit_statement alt
      | While (test, body) ->
          self#visit_expression test;
          self#visit_statement body
      | DoWhile (test, body) ->
          self#visit_statement body;
          self#visit_expression test
      | For (init, test, inc, body) ->
          (* The for-init declaration is in the enclosing scope. *)
          self#visit_statement init;
          self#env#push;
          Option.iter test ~f:self#visit_expression;
          Option.iter inc ~f:self#visit_expression;
          self#visit_statement body;
          self#env#pop
      | ForEach (_, _, _, arr_expr, body) ->
          self#env#push;
          self#visit_expression arr_expr;
          self#visit_statement body;
          self#env#pop
      | Goto _ -> ()
      | Continue -> ()
      | Break -> ()
      | Switch (e, stmts) ->
          self#visit_expression e;
          List.iter stmts ~f:self#visit_statement
      | Case e -> self#visit_expression e
      | Default -> ()
      | Return e -> Option.iter e ~f:self#visit_expression
      | Jump _ -> ()
      | Jumps e -> self#visit_expression e
      | Message _ -> ()
      | RefAssign (a, b) ->
          self#visit_expression a;
          self#visit_expression b
      | ObjSwap (a, b) ->
          self#visit_expression a;
          self#visit_expression b

    method visit_variable v =
      self#visit_type_specifier v.type_spec;
      List.iter v.array_dim ~f:self#visit_expression;
      Option.iter v.initval ~f:self#visit_expression

    method visit_fundecl f =
      self#visit_type_specifier f.return;
      List.iter f.params ~f:self#visit_variable;
      Option.iter f.body ~f:(fun body ->
          let env = new environment ctx (Some f) in
          (* v12 hoists all variable declarations in the function body
             to function scope: nested if/else branches can declare a
             local in one arm and use it in a sibling arm, and a later
             declaration is visible to earlier statements in the same
             function. Pre-walk the body collecting all VarDecls (but
             not those inside nested lambdas, which have their own
             scope) and push them onto the env BEFORE visiting any
             statement. The visit-time push_var will then add a
             duplicate entry; get_local returns the first match, which
             is fine since they reference the same record. *)
          let rec collect_decls (s : statement) =
            match s.node with
            | Declarations ds ->
                List.iter ds.vars ~f:(fun v ->
                    match v.kind with
                    | LocalVar -> env#push_var v
                    | _ -> ())
            | Compound stmts -> List.iter stmts ~f:collect_decls
            | If (_, t, e) -> collect_decls t; collect_decls e
            | While (_, body) -> collect_decls body
            | DoWhile (_, body) -> collect_decls body
            | For (init, _, _, body) -> collect_decls init; collect_decls body
            | Switch (_, stmts) -> List.iter stmts ~f:collect_decls
            | _ -> ()
          in
          List.iter body ~f:collect_decls;
          Stack.push env_stack env;
          List.iter ~f:self#visit_statement body;
          Stack.pop_exn env_stack |> ignore)

    method visit_declaration d =
      match d with
      | Global ds -> self#visit_vardecls ds
      | GlobalGroup gg -> List.iter gg.vardecls ~f:self#visit_vardecls
      | Function f | FuncTypeDef f | DelegateDef f -> self#visit_fundecl f
      | StructDef s ->
          let prev = current_struct_name in
          current_struct_name <- Some s.name;
          List.iter s.decls ~f:self#visit_struct_declaration;
          current_struct_name <- prev
      | Enum enum ->
          let visit_enumval (_, expr) =
            Option.iter expr ~f:self#visit_expression
          in
          List.iter enum.values ~f:visit_enumval

    method visit_struct_declaration d =
      match d with
      | AccessSpecifier _ -> ()
      | MemberDecl ds -> self#visit_vardecls ds
      | Constructor f -> self#visit_fundecl f
      | Destructor f -> self#visit_fundecl f
      | Method f -> self#visit_fundecl f
      | PropertyDecl _ | EventDecl _ ->
          (* Lowered to a backing field + synthetic methods at
             declaration analysis time; nothing to visit here. *)
          ()

    method visit_type_specifier (_t : type_specifier) = ()
    method visit_toplevel decls = List.iter decls ~f:self#visit_declaration
  end

let unary_op_to_string op =
  match op with
  | UPlus -> "+"
  | UMinus -> "-"
  | LogNot -> "!"
  | BitNot -> "~"
  | PreInc -> "++"
  | PreDec -> "--"
  | PostInc -> "++"
  | PostDec -> "--"
  | ForeachInc -> "++"
  | ForeachDec -> "--"

let binary_op_to_string op =
  match op with
  | Plus -> "+"
  | Minus -> "-"
  | Times -> "*"
  | Divide -> "/"
  | Modulo -> "%"
  | Equal -> "=="
  | NEqual -> "!="
  | RefEqual -> "==="
  | RefNEqual -> "!=="
  | LT -> "<"
  | GT -> ">"
  | LTE -> "<="
  | GTE -> ">="
  | LogOr -> "||"
  | LogAnd -> "&&"
  | BitOr -> "|"
  | BitXor -> "^"
  | BitAnd -> "&"
  | LShift -> "<<"
  | RShift -> ">>"

let assign_op_to_string op =
  match op with
  | EqAssign | CharAssign -> "="
  | PlusAssign -> "+="
  | MinusAssign -> "-="
  | TimesAssign -> "*="
  | DivideAssign -> "/="
  | ModuloAssign -> "%="
  | OrAssign -> "|="
  | XorAssign -> "^="
  | AndAssign -> "&="
  | LShiftAssign -> "<<="
  | RShiftAssign -> ">>="

let is_numeric = function
  | Int | Bool | LongInt | Float | Enum _ -> true
  | _ -> false

let rec jaf_type_to_string = function
  | Untyped -> "untyped"
  | Unresolved s -> "Unresolved<" ^ s ^ ">"
  | Void -> "void"
  | Int -> "int"
  | LongInt -> "lint"
  | Bool -> "bool"
  | Float -> "float"
  | String -> "string"
  | Struct (s, _) | Enum (s, _) | FuncType (Some (s, _))
  | Delegate (Some (s, _)) ->
      s
  | FuncType None -> "unknown_functype"
  | Delegate None -> "unknown_delegate"
  | Ref t -> "ref " ^ jaf_type_to_string t
  | Array _ as a -> (
      match array_base_and_rank a with
      | t, 1 -> "array@" ^ jaf_type_to_string t
      | t, rank -> sprintf "array@%s@%d" (jaf_type_to_string t) rank)
  | Wrap t -> "wrap<" ^ jaf_type_to_string t ^ ">"
  | HLLParam -> "hll_param"
  | HLLFunc -> "hll_func"
  | HLLFunc2 -> "hll_func2"
  | IMainSystem -> "IMainSystem"
  | NullType -> "null"
  | TyFunction (args, ret) | TyMethod (args, ret) ->
      sprintf "%s(%s)" (jaf_type_to_string ret)
        (String.concat ~sep:", " (List.map ~f:jaf_type_to_string args))
  | MemberPtr (s, t) -> s ^ "::" ^ jaf_type_to_string t
  | TypeUnion (a, b) ->
      sprintf "(%s | %s)" (jaf_type_to_string a) (jaf_type_to_string b)

let rec expr_to_string (e : expression) =
  let arglist_to_string args =
    let arg_to_string = Option.value_map ~default:"" ~f:expr_to_string in
    "(" ^ String.concat ~sep:", " (List.map ~f:arg_to_string args) ^ ")"
  in
  match e.node with
  | ConstInt i -> Int.to_string i
  | ConstFloat f -> Float.to_string f
  | ConstChar s -> sprintf "'%s'" s
  | ConstString s -> sprintf "\"%s\"" s
  | Ident (s, _) -> s
  | FuncAddr (s, _) -> "&" ^ s
  | MemberAddr (sname, name, _) -> sprintf "&%s::%s" sname name
  | Unary (op, e) -> (
      match op with
      | PostInc | PostDec -> expr_to_string e ^ unary_op_to_string op
      | _ -> unary_op_to_string op ^ expr_to_string e)
  | Binary (op, a, b) ->
      sprintf "%s %s %s" (expr_to_string a) (binary_op_to_string op)
        (expr_to_string b)
  | Assign (op, a, b) ->
      sprintf "%s %s %s" (expr_to_string a) (assign_op_to_string op)
        (expr_to_string b)
  | Seq (a, b) -> sprintf "%s, %s" (expr_to_string a) (expr_to_string b)
  | Ternary (a, b, c) ->
      sprintf "%s ? %s : %s" (expr_to_string a) (expr_to_string b)
        (expr_to_string c)
  | OptionalMember (obj, name, _) -> sprintf "%s?.%s" (expr_to_string obj) name
  | NullCoalesce (a, b) ->
      sprintf "%s ?? %s" (expr_to_string a) (expr_to_string b)
  | Cast (t, e) -> sprintf "(%s)%s" (jaf_type_to_string t) (expr_to_string e)
  | Subscript (e, i) -> sprintf "%s[%s]" (expr_to_string e) (expr_to_string i)
  | Member (e, s, _) -> sprintf "%s.%s" (expr_to_string e) s
  | Call (f, args, _) ->
      sprintf "%s%s" (expr_to_string f) (arglist_to_string args)
  | New ts -> sprintf "new %s" (jaf_type_to_string ts.ty)
  | NewCall (ts, args) ->
      sprintf "new %s%s" (jaf_type_to_string ts.ty) (arglist_to_string args)
  | ArrayLiteral elems ->
      sprintf "[%s]"
        (String.concat ~sep:", " (List.map elems ~f:expr_to_string))
  | DummyRef (_, e) -> expr_to_string e
  | RvalueRef e -> expr_to_string e
  | This -> "this"
  | Null -> "NULL"
  | Lambda _ -> "lambda" (* FIXME *)

let rec stmt_to_string (stmt : statement) =
  match stmt.node with
  | EmptyStatement -> ";"
  | Declarations ds -> vardecls_to_string ds
  | Expression e -> expr_to_string e ^ ";"
  | Compound stmts ->
      stmts |> List.map ~f:stmt_to_string |> List.fold ~init:"" ~f:( ^ )
  | Label label -> sprintf "%s:" label
  | If (test, body, alt) ->
      let s_test = expr_to_string test in
      let s_body = stmt_to_string body in
      let s_alt = stmt_to_string alt in
      sprintf "if (%s) %s else %s" s_test s_body s_alt
  | While (test, body) ->
      sprintf "while (%s) %s" (expr_to_string test) (stmt_to_string body)
  | DoWhile (test, body) ->
      sprintf "do %s while (%s);" (stmt_to_string body) (expr_to_string test)
  | For (init, test, inc, body) ->
      let expr_opt_to_string = Option.value_map ~default:"" ~f:expr_to_string in
      let s_init = stmt_to_string init in
      let s_test = expr_opt_to_string test in
      let s_body = stmt_to_string body in
      let s_inc = expr_opt_to_string inc in
      sprintf "for (%s %s %s) %s" s_init s_test s_inc s_body
  | ForEach (rev, var_name, ivar_name, arr_expr, body) ->
      let kw = if rev then "foreach_r" else "foreach" in
      let i = match ivar_name with Some n -> ", " ^ n | None -> "" in
      sprintf "%s (%s%s : %s) %s" kw var_name i
        (expr_to_string arr_expr) (stmt_to_string body)
  | Goto label -> sprintf "goto %s;" label
  | Continue -> "continue;"
  | Break -> "break;"
  | Switch (expr, body) ->
      let s_expr = expr_to_string expr in
      let s_body =
        body |> List.map ~f:stmt_to_string |> List.fold ~init:"" ~f:( ^ )
      in
      sprintf "switch (%s) { %s }" s_expr s_body
  | Case expr -> sprintf "case %s:" (expr_to_string expr)
  | Default -> "default:"
  | Return None -> "return;"
  | Return (Some e) -> sprintf "return %s;" (expr_to_string e)
  | Jump func -> sprintf "jump %s;" func
  | Jumps e -> sprintf "jumps %s;" (expr_to_string e)
  | Message msg -> sprintf "'%s'" msg
  | RefAssign (dst, src) ->
      sprintf "%s <- %s;" (expr_to_string dst) (expr_to_string src)
  | ObjSwap (a, b) -> sprintf "%s <=> %s;" (expr_to_string a) (expr_to_string b)

and var_to_string' d =
  let dim_iter l r = l ^ sprintf "[%s]" (expr_to_string r) in
  let dims = List.fold d.array_dim ~init:"" ~f:dim_iter in
  let init =
    match d.initval with
    | None -> ""
    | Some e -> sprintf " = %s" (expr_to_string e)
  in
  sprintf "%s %s%s%s" (jaf_type_to_string d.type_spec.ty) dims d.name init

and var_to_string d =
  let t = jaf_type_to_string d.type_spec.ty in
  sprintf "%s %s;" t (var_to_string' d)

and vardecls_to_string (decls : vardecls) =
  let vars = List.map decls.vars ~f:var_to_string' |> String.concat ~sep:", " in
  sprintf "%s %s" (jaf_type_to_string decls.typespec.ty) vars

let params_to_string = function
  | [] -> "()"
  | p :: ps ->
      let rec loop result = function
        | [] -> result
        | p :: ps -> loop (sprintf "%s, %s" result (var_to_string' p)) ps
      in
      sprintf "(%s)" (loop (var_to_string' p) ps)

let body_to_string = function
  | None -> ";"
  | Some block ->
      List.fold (List.map block ~f:stmt_to_string) ~init:"" ~f:( ^ )
      |> sprintf " { %s }"

let sdecl_to_string = function
  | AccessSpecifier Public -> "public:"
  | AccessSpecifier Private -> "private:"
  | MemberDecl ds -> vardecls_to_string ds
  | Constructor d ->
      let params = params_to_string d.params in
      let body = body_to_string d.body in
      sprintf "%s%s%s" d.name params body
  | Destructor d ->
      let params = params_to_string d.params in
      let body = body_to_string d.body in
      sprintf "~%s%s%s" d.name params body
  | Method d ->
      let return = jaf_type_to_string d.return.ty in
      let params = params_to_string d.params in
      let body = body_to_string d.body in
      sprintf "%s %s%s%s" return d.name params body
  | PropertyDecl p ->
      let accessors =
        List.map p.pd_accessors ~f:(fun (a, _) -> a ^ ";")
        |> String.concat ~sep:" "
      in
      sprintf "%s %s { %s }"
        (jaf_type_to_string p.pd_typespec.ty)
        p.pd_name accessors
  | EventDecl e ->
      sprintf "event %s %s"
        (jaf_type_to_string e.ed_typespec.ty)
        e.ed_name

let decl_to_string d =
  match d with
  | Global ds -> vardecls_to_string ds
  | GlobalGroup gg ->
      let body =
        List.fold (List.map gg.vardecls ~f:vardecls_to_string) ~init:"" ~f:( ^ )
      in
      sprintf "globalgroup %s { %s }" gg.name body
  | Function d ->
      let return = jaf_type_to_string d.return.ty in
      let params = params_to_string d.params in
      let body = body_to_string d.body in
      sprintf "%s %s%s%s" return d.name params body
  | FuncTypeDef d ->
      let return = jaf_type_to_string d.return.ty in
      let params = params_to_string d.params in
      sprintf "functype %s %s%s;" return d.name params
  | DelegateDef d ->
      let return = jaf_type_to_string d.return.ty in
      let params = params_to_string d.params in
      sprintf "delegate %s %s%s;" return d.name params
  | StructDef d ->
      let body =
        List.fold (List.map d.decls ~f:sdecl_to_string) ~init:"" ~f:( ^ )
      in
      sprintf "%s %s { %s };"
        (if d.is_class then "class" else "struct")
        d.name body
  | Enum d ->
      let enumval_to_string = function
        | s, None -> s
        | s, Some e -> sprintf "%s = %s" s (expr_to_string e)
      in
      let enumvals_fold l r = l ^ ", " ^ r in
      let body =
        List.fold
          (List.map d.values ~f:enumval_to_string)
          ~init:"" ~f:enumvals_fold
      in
      let name = match d.name with None -> "" | Some s -> s ^ " " in
      sprintf "enum %s{ %s };" name body

let ast_to_string = function
  | ASTExpression e -> expr_to_string e
  | ASTStatement s -> stmt_to_string s
  | ASTVariable v -> var_to_string v
  | ASTDeclaration d -> decl_to_string d
  | ASTStructDecl d -> sdecl_to_string d
  | ASTType t -> jaf_type_to_string t.ty

let rec jaf_to_ain_type ?ctx ?(bare_class_as_struct = false) = function
  | Untyped -> failwith "tried to convert Untyped to ain data type"
  | Unresolved s ->
      failwith ("tried to convert Unresolved to ain data type: " ^ s)
  | Void -> Ain.Type.Void
  | Int -> Ain.Type.Int
  | LongInt -> Ain.Type.LongInt
  | Bool -> Ain.Type.Bool
  | Float -> Ain.Type.Float
  | String -> Ain.Type.String
  | Struct (name, i) ->
      (* Original Rance10 emits dt=89 (IFace) for refs to interface types
         AND for params/locals typed as a class that implements an
         interface. STRUCT MEMBERS of those classes stay as dt=13
         (struct) — see SceneAssistantSelect.m_prof (struct<672>) where
         our build previously over-promoted to interface<672> and broke
         layout consistency. The [bare_class_as_struct] flag is set by
         [jaf_to_ain_struct] so member encoding matches alice. *)
      (match ctx with
       | Some c when Hashtbl.mem c.interface_names name -> Ain.Type.IFace i
       | Some c
         when not bare_class_as_struct
              && Hashtbl.mem c.iface_compatible_classes name ->
           Ain.Type.IFace i
       | _ -> Ain.Type.Struct i)
  | Enum (_, i) -> Ain.Type.Enum i
  | Array t ->
      (* Array element type: interface-compatible CLASSES stay as Struct
         in orig (e.g. [array@QuestMapObjectView] → [array<struct<621>>],
         NOT [array<interface<621>>]). Genuine interface types still
         resolve to IFace via the [interface_names] branch in the Struct
         case. Mismatched array element type breaks foreach iter-var
         dispatch: HEAD's [n] for [array@QuestMapObjectView] resolved
         to [wrap<interface<621>>] instead of [wrap<struct<621>>], so
         method calls on [n] hit interface VTABLE dispatch on a non-
         iface receiver, crashing on the iter-var read. *)
      Ain.Type.Array (jaf_to_ain_type ?ctx ~bare_class_as_struct:true t)
  | Ref (Struct (name, i)) ->
      (* Ref to a class type (implementing interface or not): encode as
         [Ref Struct], NOT [IFace]. Only bare Struct/interface refs use
         IFace. This distinguishes [new ClassImpl] dummies (Ref Struct)
         from method params [IFaceName x] (IFace + void).
         True interfaces still unwrap to IFace (Ain rejects [Ref IFace]). *)
      (match ctx with
       | Some c when Hashtbl.mem c.interface_names name -> Ain.Type.IFace i
       | _ -> Ain.Type.Ref (Ain.Type.Struct i))
  | Ref t -> Ain.Type.Ref (jaf_to_ain_type ?ctx t)
  | Wrap t ->
      (* [Wrap inner] is the foreach iter-var binding shape. Keep
         interface-compatible classes as Struct here for the same
         reason as Array (above). *)
      Ain.Type.Wrap (jaf_to_ain_type ?ctx ~bare_class_as_struct:true t)
  | HLLParam -> Ain.Type.HLLParam
  | HLLFunc -> Ain.Type.HLLFunc
  | HLLFunc2 -> Ain.Type.HLLFunc2
  | Delegate (Some (_, i)) -> Ain.Type.Delegate i
  | Delegate None -> Ain.Type.Delegate (-1)
  | FuncType (Some (_, i)) -> Ain.Type.FuncType i
  | FuncType None -> Ain.Type.FuncType (-1)
  | IMainSystem -> Ain.Type.IMainSystem
  | NullType -> Ain.Type.NullType
  | TyFunction _ -> Ain.Type.Function
  | TyMethod _ -> Ain.Type.Method
  | MemberPtr _ -> Ain.Type.Int (* slot number *)
  | TypeUnion _ -> failwith "tried to convert TypeUnion to ain data type"

let rec ain_to_jaf_type ain = function
  | Ain.Type.Void -> Void
  | Int -> Int
  | LongInt -> LongInt
  | Bool -> Bool
  | Float -> Float
  | String -> String
  | Struct -1 -> Struct ("struct", -1)
  | Struct i -> Struct ((Ain.get_struct_by_index ain i).name, i)
  | IFace -1 -> Struct ("interface", -1)
  | IFace i -> Struct ((Ain.get_struct_by_index ain i).name, i)
  | Enum i -> Enum (Ain.get_enum_name_by_index ain i, i)
  | Enum2 i -> Enum (Ain.get_enum_name_by_index ain i, i)
  | Array t -> Array (ain_to_jaf_type ain t)
  | Ref t -> Ref (ain_to_jaf_type ain t)
  | Wrap t -> Wrap (ain_to_jaf_type ain t)
  | HLLParam -> HLLParam
  | HLLFunc -> HLLFunc
  | HLLFunc2 -> HLLFunc2
  | Delegate -1 -> Delegate None
  | Delegate i -> Delegate (Some ((Ain.get_delegate_by_index ain i).name, i))
  | FuncType -1 -> FuncType None
  | FuncType i -> FuncType (Some ((Ain.get_functype_by_index ain i).name, i))
  | IMainSystem -> IMainSystem
  | t ->
      Printf.failwithf "cannot convert %s to jaf type" (Ain.Type.to_string t) ()

let jaf_to_ain_variables ?ctx ?(iface_padding = false)
    ?(wrap_ref_params = false) ?(bare_class_as_struct = false) j_p =
  (* [iface_padding=true] (set by jaf_to_ain_function for v12 params):
     interface-typed params get a void padding slot matching the
     ref-scalar pattern. Original Rance10's
     [void ReleaseComponent(IUserComponent c)] has nargs=2 vars=2
     with [IFace + <void>]. Struct members get padding elsewhere
     (inject_iface_padding_into_decl) so this flag must be FALSE
     for jaf_to_ain_struct. *)
  let is_iface_ty ty =
    match ctx with
    | None -> false
    | Some c ->
        let is_true_iface n = Hashtbl.mem c.interface_names n in
        let is_iface_compat_class n =
          Hashtbl.mem c.iface_compatible_classes n
        in
        let rec walk = function
          | Unresolved name -> is_true_iface name || is_iface_compat_class name
          | Struct (name, _) -> is_true_iface name || is_iface_compat_class name
          | Ref (Unresolved name) -> is_true_iface name
          | Ref (Struct (name, _)) -> is_true_iface name
          | Ref t -> walk t
          | _ -> false
        in
        walk ty
  in
  let wrap_ref_type = function
    | Ref inner when wrap_ref_params ->
        Some (Ain.Type.Wrap (jaf_to_ain_type ?ctx inner))
    | _ -> None
  in
  let needs_void ty =
    is_ref_scalar ty || (iface_padding && is_iface_ty ty)
    || Option.is_some (wrap_ref_type ty)
  in
  let rec convert_params (params : variable list) (result : Ain.Variable.t list)
      index =
    match params with
    | [] -> List.rev result
    | x :: xs ->
        let value_type =
          match wrap_ref_type x.type_spec.ty with
          | Some t -> t
          | None -> jaf_to_ain_type ?ctx ~bare_class_as_struct x.type_spec.ty
        in
        let var = Ain.Variable.make ~index x.name value_type in
        if needs_void x.type_spec.ty then
          let void = Ain.Variable.make ~index:(index + 1) "<void>" Void in
          convert_params xs (void :: var :: result) (index + 2)
        else convert_params xs (var :: result) (index + 1)
  in
  convert_params j_p [] 0

let jaf_to_ain_function ?ctx (j_f : fundecl) (a_f : Ain.Function.t) =
  let iface_padding =
    match ctx with
    | Some c -> Ain.version_gte c.ain (12, 0)
    | None -> false
  in
  let wrap_ref_params =
    match ctx with
    | Some c ->
        Ain.version_gte c.ain (12, 0)
        && (String.is_suffix j_f.name ~suffix:"::postset"
           || String.is_suffix j_f.name ~suffix:"::preset")
    | None -> false
  in
  let vars =
    jaf_to_ain_variables ?ctx ~iface_padding ~wrap_ref_params j_f.params
  in
  {
    a_f with
    vars;
    nr_args = List.length vars;
    return_type = jaf_to_ain_type ?ctx j_f.return.ty;
    is_label = j_f.is_label;
    is_lambda = j_f.is_lambda;
  }

let jaf_to_ain_struct ?ctx j_s (a_s : Ain.Struct.t) =
  let members =
    List.filter_map j_s.decls ~f:(function
      | MemberDecl ds when not ds.is_const_decls -> Some ds.vars
      | _ -> None)
    |> List.concat
    |> jaf_to_ain_variables ?ctx ~bare_class_as_struct:true
  in
  (* v12: orig writes [name2 = ""] for 21 specific (struct, member)
     pairs. Hardcoded list mirrors orig; rule isn't fully understood. *)
  let members =
    match ctx with
    | Some c when Ain.version_gte c.ain (12, 0) ->
        let needs_empty_n2 (m : Ain.Variable.t) =
          List.mem
            [
              "PlayerCardSkill", "m_instance";
              "Quest", "m_questMap";
              "FriendPhaseList", "m_list";
              "AssistantMessageCollection", "m_message";
              "LeaderCard", "m_skillCache";
              "OrganizationCardCollection", "m_swapCard";
              "PlayerCardCollection", "m_onAddCard";
              "PlayerCard", "m_funcGetStar";
              "NewMarkFlagGlobal", "OnChangeEvent";
              "NewMarkFlagLocal", "OnChangeEvent";
              "NgPlayerCardManager", "OnChangeEvent";
              "LeaderState", "m_onChange";
              "PartyBonusSwitcher", "m_onChange";
              "Assistant", "<m_onChangeStandEvent>";
              "Assistant", "<m_onPlayMessageEvent>";
              "AssistantSelector", "<OnChangeAssistantEvent>";
              "AssistantSelector", "<OnChangeStandEvent>";
              "AssistantSelector", "<OnPlayMessageEvent>";
              "Party", "<OnChangeHpEvent>";
              "OrganizationCardCollection", "<OnAddEvent>";
              "GameConfig", "<IsEnableBattleTimeScaling>";
            ]
            ~equal:(fun (a, b) (c, d) ->
              String.equal a c && String.equal b d)
            (j_s.name, m.name)
        in
        ignore c;
        List.map members ~f:(fun m ->
            if needs_empty_n2 m then { m with name2 = Some "" } else m)
    | _ -> members
  in
  let constructor =
    match
      List.find j_s.decls ~f:(function
        | Constructor ctor -> List.is_empty ctor.params
        | _ -> false)
    with
    | Some (Constructor ctor) -> Option.value_exn ctor.index
    | _ -> -1
  in
  let is_dtor = function Destructor _ -> true | _ -> false in
  let destructor =
    match List.find j_s.decls ~f:is_dtor with
    | Some (Destructor dtor) -> Option.value_exn dtor.index
    | _ -> -1
  in
  {
    a_s with
    members;
    constructor;
    destructor
    (* TODO: interfaces *)
    (* TODO: vmethods *);
  }

let jaf_to_ain_functype ?ctx j_f =
  let iface_padding =
    match ctx with
    | Some c -> Ain.version_gte c.ain (12, 0)
    | None -> false
  in
  let variables = jaf_to_ain_variables ?ctx ~iface_padding j_f.params in
  (* v12: rename anonymous template-delegate params to "arg" / "argN"
     to match original. Source like [delegate bool DG_Func<string,bool>
     (string);] declares params without names; our parser fills in
     "<anonymous>" but original v12 uses "arg" (single) or
     "arg1"/"arg2"/... (multiple). Don't touch [<void>] padding slots. *)
  let variables =
    match ctx with
    | Some c when Ain.version_gte c.ain (12, 0) ->
        let real_params =
          List.filter variables ~f:(fun (v : Ain.Variable.t) ->
              not (String.equal v.name "<void>"))
        in
        let n_real = List.length real_params in
        let counter = ref 0 in
        List.map variables ~f:(fun (v : Ain.Variable.t) ->
            if String.equal v.name "<void>" then v
            else if String.equal v.name "<anonymous>" then (
              Int.incr counter;
              let new_name =
                if n_real = 1 then "arg"
                else Printf.sprintf "arg%d" !counter
              in
              { v with name = new_name; name2 = Some new_name })
            else (
              Int.incr counter;
              v))
    | _ -> variables
  in
  Ain.FunctionType.
    {
      name = j_f.name;
      index = Option.value_exn j_f.index;
      variables;
      nr_arguments = List.length variables;
      return_type = jaf_to_ain_type ?ctx j_f.return.ty;
    }

let jaf_to_ain_hll_function j_f =
  let jaf_to_ain_hll_argument (param : variable) =
    Ain.Library.Argument.create param.name (jaf_to_ain_type param.type_spec.ty)
  in
  let return_type = jaf_to_ain_type j_f.return.ty in
  let arguments = List.map j_f.params ~f:jaf_to_ain_hll_argument in
  Ain.Library.Function.create j_f.name return_type arguments

let ain_to_jaf_variable ain kind (v : Ain.Variable.t) =
  {
    name = v.name;
    location = dummy_location;
    array_dim = [] (* FIXME *);
    is_const = false;
    is_private = false;
    kind;
    type_spec =
      { ty = ain_to_jaf_type ain v.value_type; location = dummy_location };
    initval = None;
    index = Some v.index;
  }

(* v11 foreach desugar machinery. [foreach (var : array)] is rewritten
   into a [while] loop with a synthetic counter and a synthetic alias
   to the container so the surrounding type-resolution / codegen
   passes don't need to know about [ForEach] directly. The counter
   uses [ForeachInc]/[ForeachDec] in the loop test so codegen can
   detect "this is the foreach pre-test increment" and emit the
   matching original compiler bytecode. *)
let foreach_counter = ref 0

let desugar_foreach_stmt loc rev var_name ivar_name (arr_expr : expression)
    (body : statement) =
  let id =
    foreach_counter := !foreach_counter + 1;
    !foreach_counter
  in
  let counter_name =
    match ivar_name with
    | Some name -> name
    | None -> Printf.sprintf "<foreach_i_%d>" id
  in
  let container_name = Printf.sprintf "<foreach_container_%d>" id in
  let dl = dummy_location in
  let mk_expr node = { ty = Untyped; node; loc = dl } in
  let mk_stmt node = { node; delete_vars = []; loc } in
  let mk_ts ty = { ty; location = dl } in
  let counter_id = mk_expr (Ident (counter_name, UnresolvedIdent)) in
  let container_id = mk_expr (Ident (container_name, UnresolvedIdent)) in
  let numof_call =
    mk_expr
      (Call
         ( mk_expr (Member (container_id, "Numof", UnresolvedMember)),
           [],
           UnresolvedCall ))
  in
  let counter_init_val =
    if rev then numof_call else mk_expr (ConstInt (-1))
  in
  let mk_var name ty =
    {
      name;
      location = dl;
      array_dim = [];
      is_const = false;
      is_private = false;
      kind = LocalVar;
      type_spec = mk_ts ty;
      initval = None;
      index = None;
    }
  in
  let counter_alloc =
    mk_stmt
      (Declarations
         {
           decl_loc = dl;
           is_const_decls = false;
           typespec = mk_ts Int;
           vars = [ { (mk_var counter_name Int) with is_private = true } ];
         })
  in
  let container_expr =
    match arr_expr.node with
    (* v12: ArrayLiteral foreach source is an rvalue — wrap with
       RvalueRef so the Ref-typed container init has an lvalue to
       point at. *)
    | Call _ | ArrayLiteral _ -> { arr_expr with node = RvalueRef arr_expr }
    | _ -> arr_expr
  in
  let container_init =
    mk_stmt
      (Declarations
         {
           decl_loc = dl;
           is_const_decls = false;
           typespec = mk_ts (Ref (Array HLLParam));
           vars =
             [
               {
                 (mk_var container_name (Ref (Array HLLParam))) with
                 is_private = true;
                 initval = Some container_expr;
               };
             ];
         })
  in
  let counter_init =
    mk_stmt
      (Declarations
         {
           decl_loc = dl;
           is_const_decls = false;
           typespec = mk_ts Int;
           vars =
             [
               {
                 (mk_var counter_name Int) with
                 is_private = true;
                 initval = Some counter_init_val;
               };
             ];
         })
  in
  let while_cond =
    if rev then
      mk_expr
        (Binary
           ( GTE,
             mk_expr (Unary (ForeachDec, counter_id)),
             mk_expr (ConstInt 0) ))
    else
      mk_expr (Binary (LT, mk_expr (Unary (ForeachInc, counter_id)), numof_call))
  in
  let var_decl =
    mk_stmt
      (Declarations
         {
           decl_loc = dl;
           is_const_decls = false;
           typespec = mk_ts (Wrap HLLParam);
           vars = [ mk_var var_name (Wrap HLLParam) ];
         })
  in
  let var_ref_assign =
    mk_stmt
      (RefAssign
         ( mk_expr (Ident (var_name, UnresolvedIdent)),
           mk_expr (Subscript (container_id, counter_id)) ))
  in
  let body_stmts =
    match body.node with Compound stmts -> stmts | _ -> [ body ]
  in
  let while_body = mk_stmt (Compound (var_ref_assign :: body_stmts)) in
  let while_stmt = mk_stmt (While (while_cond, while_body)) in
  mk_stmt
    (Compound [ counter_alloc; var_decl; container_init; counter_init; while_stmt ])

let rec desugar_foreach_in_stmt (stmt : statement) =
  match stmt.node with
  | ForEach (rev, var_name, ivar_name, arr_expr, body) ->
      desugar_foreach_in_stmt
        (desugar_foreach_stmt stmt.loc rev var_name ivar_name arr_expr body)
  | Compound stmts ->
      { stmt with node = Compound (List.map stmts ~f:desugar_foreach_in_stmt) }
  | If (test, then_, else_) ->
      {
        stmt with
        node =
          If
            ( desugar_foreach_in_expr test,
              desugar_foreach_in_stmt then_,
              desugar_foreach_in_stmt else_ );
      }
  | While (test, body) ->
      {
        stmt with
        node =
          While (desugar_foreach_in_expr test, desugar_foreach_in_stmt body);
      }
  | DoWhile (test, body) ->
      {
        stmt with
        node =
          DoWhile (desugar_foreach_in_expr test, desugar_foreach_in_stmt body);
      }
  | For (init, test, inc, body) ->
      { stmt with node = For (init, test, inc, desugar_foreach_in_stmt body) }
  | Switch (expr, stmts) ->
      {
        stmt with
        node =
          Switch
            (desugar_foreach_in_expr expr, List.map stmts ~f:desugar_foreach_in_stmt);
      }
  | Expression e -> { stmt with node = Expression (desugar_foreach_in_expr e) }
  | Return (Some e) -> { stmt with node = Return (Some (desugar_foreach_in_expr e)) }
  | RefAssign (a, b) ->
      {
        stmt with
        node = RefAssign (desugar_foreach_in_expr a, desugar_foreach_in_expr b);
      }
  | _ -> stmt

(* Walk expressions for nested lambdas, descending into the lambda body
   so foreach loops inside captured handlers also get desugared. *)
and desugar_foreach_in_expr (e : expression) =
  let rec walk (e : expression) =
    (match e.node with
     | Lambda f ->
         f.body <- Option.map f.body ~f:(List.map ~f:desugar_foreach_in_stmt)
     | Unary (_, inner) -> walk inner
     | Binary (_, a, b) -> walk a; walk b
     | Assign (_, a, b) -> walk a; walk b
     | Seq (a, b) -> walk a; walk b
     | Ternary (a, b, c) -> walk a; walk b; walk c
     | NullCoalesce (a, b) -> walk a; walk b
     | Cast (_, inner) -> walk inner
     | Subscript (a, b) -> walk a; walk b
     | Member (inner, _, _) -> walk inner
     | OptionalMember (inner, _, _) -> walk inner
     | Call (f, args, _) ->
         walk f;
         List.iter args ~f:(Option.iter ~f:walk)
     | NewCall (_, args) ->
         List.iter args ~f:(Option.iter ~f:walk)
     | ArrayLiteral elems -> List.iter elems ~f:walk
     | DummyRef (_, inner) -> walk inner
     | RvalueRef inner -> walk inner
     | _ -> ())
  in
  walk e;
  e

let desugar_foreach_in_fundecl (f : fundecl) =
  f.body <- Option.map f.body ~f:(List.map ~f:desugar_foreach_in_stmt)

let desugar_foreach decls =
  List.iter decls ~f:(function
    | Function f | FuncTypeDef f | DelegateDef f ->
        desugar_foreach_in_fundecl f
    | StructDef s ->
        List.iter s.decls ~f:(function
          | Method f | Constructor f | Destructor f ->
              desugar_foreach_in_fundecl f
          | _ -> ())
    | _ -> ())

let context_from_ain ?(constants : variable list = []) ain =
  let ain_to_jaf_functype (f : Ain.FunctionType.t) =
    {
      name = f.name;
      loc = dummy_location;
      return =
        { ty = ain_to_jaf_type ain f.return_type; location = dummy_location };
      params =
        List.map (Ain.FunctionType.logical_parameters f) ~f:(fun v ->
            ain_to_jaf_variable ain Parameter v);
      body = None;
      is_label = false;
      is_lambda = false;
      is_private = false;
      index = Some f.index;
      class_name = None;
      class_index = None;
    }
  in
  let globals = Hashtbl.create (module String) in
  let structs = Hashtbl.create (module String) in
  let functions = Hashtbl.create (module String) in
  let overloads = Hashtbl.create (module String) in
  let functypes = Hashtbl.create (module String) in
  let delegates = Hashtbl.create (module String) in
  let libraries = Hashtbl.create (module String) in
  let user_bodied_accessors = Hashtbl.create (module String) in
  let properties_with_backing_ref = Hashtbl.create (module String) in
  let nullable_ref_properties = Hashtbl.create (module String) in
  let structs_with_constructor = Hashtbl.create (module String) in
  let structs_with_default_constructor = Hashtbl.create (module String) in
  List.iter constants ~f:(fun v -> Hashtbl.add_exn globals ~key:v.name ~data:v);
  Ain.global_iter ain ~f:(fun g ->
      Hashtbl.add_exn globals ~key:g.variable.name
        ~data:(ain_to_jaf_variable ain GlobalVar g.variable));
  Ain.struct_iter ain ~f:(fun s ->
      let struc =
        {
          name = s.name;
          loc = dummy_location;
          index = s.index;
          members = Hashtbl.create (module String);
          properties = Hashtbl.create (module String);
        }
      in
      List.iter s.members ~f:(function
        | { value_type = Void; _ } -> () (* dummy slot *)
        | v ->
            Hashtbl.add_exn struc.members ~key:v.name
              ~data:(ain_to_jaf_variable ain ClassVar v));
      Hashtbl.add_exn structs ~key:s.name ~data:struc);
  Ain.function_iter ain ~f:(fun (f : Ain.Function.t) ->
      let class_name, class_index =
        match String.lsplit2 f.name ~on:'@' with
        | None -> (None, None)
        | Some (left, _) -> (Some left, Ain.get_struct_index ain left)
      in
      let func =
        {
          name = f.name;
          loc = dummy_location;
          return =
            {
              ty = ain_to_jaf_type ain f.return_type;
              location = dummy_location;
            };
          params =
            List.map (Ain.Function.logical_parameters f) ~f:(fun v ->
                ain_to_jaf_variable ain Parameter v);
          body = None;
          is_label = f.is_label;
          is_lambda = f.is_lambda;
          is_private = false;
          index = Some f.index;
          class_name;
          class_index;
        }
      in
      (* v11 may have multiple ain entries sharing a mangled name
         (overloaded methods / functions). The first goes into
         [functions]; subsequent same-name entries land in [overloads]
         so call-site resolution can pick by parameter types. *)
      match Hashtbl.find functions f.name with
      | None -> Hashtbl.set functions ~key:f.name ~data:func
      | Some _ ->
          Hashtbl.update overloads f.name ~f:(function
            | None -> [ func ]
            | Some xs -> func :: xs));
  Ain.functype_iter ain ~f:(fun (f : Ain.FunctionType.t) ->
      Hashtbl.add_exn functypes ~key:f.name ~data:(ain_to_jaf_functype f));
  Ain.delegate_iter ain ~f:(fun (f : Ain.FunctionType.t) ->
      Hashtbl.add_exn delegates ~key:f.name ~data:(ain_to_jaf_functype f));
  Ain.library_iter ain ~f:(fun (l : Ain.Library.t) ->
      let functions = Hashtbl.create (module String) in
      let lib_overloads = Hashtbl.create (module String) in
      Array.iter l.functions ~f:(fun (f : Ain.Library.Function.t) ->
          let func =
            {
              name = f.name;
              loc = dummy_location;
              return =
                {
                  ty = ain_to_jaf_type ain f.return_type;
                  location = dummy_location;
                };
              params =
                List.map f.arguments ~f:(fun v ->
                    {
                      name = v.name;
                      location = dummy_location;
                      array_dim = [] (* FIXME *);
                      is_const = false;
                      is_private = false;
                      kind = Parameter;
                      type_spec =
                        {
                          ty = ain_to_jaf_type ain v.value_type;
                          location = dummy_location;
                        };
                      initval = None;
                      index = None;
                    });
              body = None;
              is_label = false;
              is_lambda = false;
              is_private = false;
              index = Some f.index;
              class_name = None;
              class_index = None;
            }
          in
          (* v11 HLL libraries may have multiple entries with the same
             name. The first goes in [functions]; later same-name entries
             append to [overloads]. *)
          match Hashtbl.find functions f.name with
          | None -> Hashtbl.set functions ~key:f.name ~data:func
          | Some _ ->
              Hashtbl.update lib_overloads f.name ~f:(function
                | None -> [ func ]
                | Some xs -> func :: xs));
      Hashtbl.add_exn libraries ~key:l.name
        ~data:{ hll_name = l.name; functions; overloads = lib_overloads });
  let version = (Ain.version ain * 100) + Ain.minor_version ain in
  let reference_delegate_order, reference_array_delegates =
    let path = Stdlib.Filename.concat "ain" "Rance10_original" in
    let path = Stdlib.Filename.concat path "Rance10.ain" in
    if Ain.version ain >= 12 && Stdlib.Sys.file_exists path then (
      let ref_ain = Ain.load path in
      let order = ref [] in
      let arrays = Hashtbl.create (module String) in
      Ain.delegate_iter ref_ain ~f:(fun (ft : Ain.FunctionType.t) ->
          order := ft.name :: !order;
          if String.is_prefix ft.name ~prefix:"<Array" then
            let f =
              {
                name = ft.name;
                loc = dummy_location;
                return =
                  {
                    ty = ain_to_jaf_type ref_ain ft.return_type;
                    location = dummy_location;
                  };
                params =
                  List.map (Ain.FunctionType.logical_parameters ft)
                    ~f:(ain_to_jaf_variable ref_ain Parameter);
                body = None;
                is_label = false;
                is_lambda = false;
                is_private = false;
                index = None;
                class_name = None;
                class_index = None;
              }
            in
            Hashtbl.set arrays ~key:ft.name ~data:f);
      (List.rev !order, Some arrays))
    else ([], None)
  in
  {
    ain;
    version;
    globals;
    structs;
    functions;
    overloads;
    functypes;
    delegates;
    libraries;
    user_bodied_accessors;
    properties_with_backing_ref;
    v12_pending_property_stubs = Hashtbl.create (module String);
    v12_property_stub_classes_emitted = Hashtbl.create (module String);
    v12_property_getter_dup_indices = Hashtbl.create (module Int);
    v12_class_interfaces = Hashtbl.create (module String);
    v12_struct_methods = Hashtbl.create (module String);
    v12_body_dup_indices = Hashtbl.create (module Int);
    v12_pending_lambdas = Queue.create ();
    v12_current_body_group = ref None;
    v12_current_body_file_no = ref None;
    v12_pending_interface_proto_groups = Queue.create ();
    v12_pending_interface_proto_seen = Hashtbl.create (module String);
    v12_allocated_interface_proto_groups = Hashtbl.create (module String);
    v12_structs_with_member_initvals = Hashtbl.create (module String);
    nullable_ref_properties;
    structs_with_constructor;
    structs_with_default_constructor;
    enum_values = Hashtbl.create (module String);
    enum_types = Hashtbl.create (module String);
    interface_names = Hashtbl.create (module String);
    iface_compatible_classes = Hashtbl.create (module String);
    delegate_names = Hashtbl.create (module String);
    v12_reference_array_delegates = reference_array_delegates;
    v12_reference_delegate_order = reference_delegate_order;
    v12_reference_delegate_cursor = ref 0;
    interface_parent = Hashtbl.create (module String);
    interface_inherited_methods = Hashtbl.create (module String);
  }
