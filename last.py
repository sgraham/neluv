from dataclasses import dataclass

@dataclass
class Number:
  value: int

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
  type: object
  name: str
  params: list[object]
  body: Block

@dataclass
class Type:
  name: str

@dataclass
class TypedParam:
  type: Type
  name: str

@dataclass
class MacroCallWithBlock:
  func: FuncCall
  body: Block

@dataclass
class VarDecl:
  type: object
  name: str
  init: object

@dataclass
class FieldReference:
  lhs: object
  rhs: str

#import inspect
#inspect.currentframe().f_back.f_locals
def parse(code):
  """Turns a string into an AST."""
  print('CODE', code)
  print(inspect.currentframe().f_back.f_locals)
