from dataclasses import dataclass

class AstNode:
  line: int
  column: int
  def copy_meta(self, source):
    self.line = source.line
    self.column = source.column

@dataclass
class Number(AstNode):
  value: int

@dataclass
class String(AstNode):
  value: str

@dataclass
class Fstring(AstNode):
  value: str

@dataclass
class Const(AstNode):
  name: str

@dataclass
class FuncCall(AstNode):
  func: AstNode
  args: list[AstNode]

@dataclass
class Ident(AstNode):
  name: str

  def __post_init__(self):
    self.special = False

@dataclass
class TIdent(AstNode):
  name: str

  def __post_init__(self):
    self.special = False

@dataclass
class JoinIdents(AstNode):
  idents: list[AstNode]  # Must be Idents or TIdents

@dataclass
class Op(AstNode):
  name: str

@dataclass
class GetAttr(AstNode):
  lhs: AstNode
  rhs: str

@dataclass
class Assign(AstNode):
  lhs: AstNode
  rhs: AstNode

@dataclass
class AugAssign(AstNode):
  lhs: AstNode
  op: AstNode
  rhs: AstNode

@dataclass
class Block(AstNode):
  entries: list[AstNode]

@dataclass
class TopLevel(AstNode):
  body: Block

@dataclass
class Package(AstNode):
  name: str
  globals: dict[str, AstNode]

@dataclass
class Type(AstNode):
  # Can be:
  # - an entry in _KEYWORDS (for basic types)
  # - a reference to another Type (for pointer-to, etc.)
  # - a reference an AstNode for a user-defined type
  base: object

@dataclass
class SymTabEntry:  # Not AstNode
  type: Type
  ref_node: AstNode  # For error reporting
  is_func_param: bool = False
  is_declared_local: bool = False
  is_upval: bool = False
  is_global: bool = False
  is_pending_nonlocal: bool = False
  is_hoisted_function: bool = False
  func_ref_if_upval: AstNode = None
  is_compiler_temporary: bool = False

upval_binding_counter = 0
class UpvalBindings:  # Not AstNode
  def __init__(self, to_bind, func_name):
    self.to_bind = to_bind  # map of ident to ste's to bind
    self.struct_name = '$Upvals$' + func_name
    mems = [TypedVar(ste.type, n) for n,ste in to_bind.items()]
    self.struct = Struct(Ident(self.struct_name), mems)
    global upval_binding_counter
    self.parent_binding_name = '$uv' + str(upval_binding_counter)
    upval_binding_counter += 1

@dataclass
class FuncDef(AstNode):
  rtype: AstNode
  name: str
  params: list[AstNode]
  body: Block
  # True when hoisted out of another function, and so shouldn't be visible in
  # the namespace to which it was moved.
  hidden: bool = False

  def __post_init__(self):
    self.symtabs = []  # stack of dicts, where keys are names and values are SymTabEntry
    self.upval_bindings = {}  # names are funcname, values are UpvalBindings
    self.nested_funcs_to_push_upvals = []

  def push_empty_symtab_scope(self):
    self.symtabs.append({})

  def pop_symtab_scope(self):
    self.symtabs.pop()

  def add_to_symtab(self, name, ste):
    #print('ADDING', name, 'to', self.name)
    assert name not in self.symtabs[-1]
    self.symtabs[-1][name] = ste

  def replace_in_symtab(self, name, ste):
    #print('REPLACING', name, 'in', self.name)
    assert name in self.symtabs[-1]
    self.symtabs[-1][name] = ste

  def find_in_symtab(self, name):
    #print('FINDING', name, 'in', self.name)
    for symtab in reversed(self.symtabs):
      x = symtab.get(name)
      if x: return x
    return None

  def clone(self):
    return FuncDef(self.rtype, self.name, self.params, self.body, self.hidden)

@dataclass
class ImportMacros(AstNode):
  filename: str

@dataclass
class Quote(AstNode):
  name: str
  body: Block

@dataclass
class ImportPackage(AstNode):
  what: AstNode
  renamed: AstNode

@dataclass
class ImportItem(AstNode):
  what: AstNode
  renamed: AstNode

@dataclass
class Import(AstNode):
  package: ImportPackage
  items: list[ImportItem]

@dataclass
class ImportFrom(AstNode):
  package: ImportPackage
  items: list[ImportItem]

@dataclass
class MacroDef(AstNode):
  name: str
  pyfunc: object

@dataclass
class FuncType(Type):
  rtype: AstNode
  params: list[AstNode]

@dataclass
class ListDecl(Type):
  pass

@dataclass
class FixedArrayDecl(Type):
  size: AstNode

@dataclass
class PointerDecl(Type):
  pass

@dataclass
class OptionalDecl(Type):
  pass

@dataclass
class MacroCallWithBlock(AstNode):
  func: FuncCall
  body: Block

@dataclass
class Assert(AstNode):
  expr: AstNode
  message: AstNode

@dataclass
class Return(AstNode):
  value: AstNode

@dataclass
class Del(AstNode):
  exprs: list[AstNode]

@dataclass
class Break(AstNode):
  pass

@dataclass
class Continue(AstNode):
  pass

@dataclass
class Pass(AstNode):
  pass

@dataclass
class External(AstNode):
  pass

@dataclass
class Nonlocal(AstNode):
  vars: list[str]

@dataclass
class For(AstNode):
  it: AstNode
  collection: AstNode
  body: Block
  els: Block

@dataclass
class While(AstNode):
  cond: AstNode
  body: Block
  els: Block

@dataclass
class Elif(AstNode):
  cond: AstNode
  body: Block

@dataclass
class If(AstNode):
  cond: AstNode
  body: Block
  elifs: list[Elif]
  els: Block

@dataclass
class OptionalUnwrap(AstNode):
  optexpr: AstNode
  bind: str

@dataclass
class TypedVar(AstNode):
  type: Type
  name: str

@dataclass
class VarDecl(AstNode):
  type: AstNode
  name: str
  init: AstNode

@dataclass
class UnaryExpr(AstNode):
  op: AstNode
  obj: AstNode

@dataclass
class Expr(AstNode):
  # 3 + 2n long:
  #   VAL0 op0 VAL1 [op1 VAL2 ...]
  chain: list[AstNode]

@dataclass
class And(AstNode):
  tests: list[AstNode]

@dataclass
class Or(AstNode):
  tests: list[AstNode]

@dataclass
class CompExpr(AstNode):
  # 3 + 2n long:
  #   VAL0 cmp0 VAL1 [cmp1 VAL2 ...]
  # for x < y < z
  # === x < y and y < z, but y only eval once.
  chain: list[AstNode]

@dataclass
class PackageReference(AstNode):
  lhs: AstNode
  rhs: AstNode

@dataclass
class GetItem(AstNode):
  obj: AstNode
  index: AstNode

@dataclass
class Struct(AstNode):
  name: str
  members: list[TypedVar]

  def __post_init__(self):
    self._cached_type = None
    self.omit_constructor = False

  def cached_type(self):
    if self._cached_type == None:
      self._cached_type = Type(self)
    return self._cached_type

@dataclass
class Union(AstNode):
  name: str
  members: list[Type]

@dataclass
class On(AstNode):
  name: str
  block: Block

@dataclass
class Tuple(AstNode):
  items: list[AstNode]

@dataclass
class List(AstNode):
  values: list[AstNode]

@dataclass
class Comprehension(AstNode):
  result: AstNode
  fors: list[AstNode]
  ifs: list[AstNode]

@dataclass
class ComprehensionFor(AstNode):
  its: list[AstNode]
  thing: AstNode

@dataclass
class ListComprehension(AstNode):
  body: AstNode

@dataclass
class ParseError:
  line: int
  column: int
  got: AstNode
