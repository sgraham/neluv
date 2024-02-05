import last
import pprint

#struct Enumerator_ListInt:
  #*[]int seq
  #int cur

def enumerate(macro):
  pprint.pprint(macro.args)
  pprint.pprint(macro.func)
  pprint.pprint(macro.func.symtab)
  return last.List([last.Number(0), last.Number(1), last.Number(2)])
