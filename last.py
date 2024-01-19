from dataclasses import dataclass

@dataclass
class Number:
  value: int

@dataclass
class String:
  value: str

@dataclass
class Const:
  name: str

@dataclass
class FuncCall:
  func: object
  args: list[object]

@dataclass
class Ident:
  name: object

@dataclass
class Op:
  name: str

@dataclass
class GetAttr:
  lhs: object
  rhs: str

@dataclass
class Assign:
  lhs: object
  rhs: object

@dataclass
class Block:
  entries: list[object]

@dataclass
class TopLevel:
  body: Block

@dataclass
class FuncDef:
  rtype: object
  name: str
  params: list[object]
  body: Block

@dataclass
class Type:
  base: object

@dataclass
class FuncType(Type):
  rtype: object
  params: list[object]

@dataclass
class SliceDecl(Type):
  pass

@dataclass
class FixedArrayDecl(Type):
  size: object

@dataclass
class PointerDecl(Type):
  pass

@dataclass
class MacroCallWithBlock:
  func: FuncCall
  body: Block

@dataclass
class Return:
  value: object

@dataclass
class Pass:
  pass

@dataclass
class For:
  it: object
  collection: object
  body: Block
  els: Block

@dataclass
class TypedVar:
  type: Type
  name: str

@dataclass
class VarDecl:
  type: object
  name: str
  init: object

@dataclass
class UnaryExpr:
  op: object
  obj: object

@dataclass
class BinaryExpr:
  lhs: object
  rhs: object
  op: object

@dataclass
class CompExpr:
  # 3 + 2n long:
  #   VAL0 cmp0 VAL1 [cmp1 VAL2 ...]
  # for x < y < z
  # === x < y and y < z, but y only eval once.
  chain: list[object]

@dataclass
class PackageReference:
  lhs: object
  rhs: object

@dataclass
class GetItem:
  obj: object
  index: object

@dataclass
class Struct:
  name: str
  members: list[Type]

@dataclass
class ParseError:
  line: int
  column: int
  got: object
