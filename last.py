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
class TypedParam:
  type: Type
  name: str

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
class VarDecl:
  type: object
  name: str
  init: object

@dataclass
class FieldReference:
  lhs: object
  rhs: str

@dataclass
class ParseError:
  line: int
  column: int
  got: object
