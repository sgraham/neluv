import last
import pprint

def enumerate(macro):
  pprint.pprint(macro.args)
  pprint.pprint(macro.func)
  pprint.pprint(macro.func.symtab)
  TEST_STUFF =
'''
struct Enumerator_ListInt:
  *[]int seq
  int cur

def Enumerator_ListInt
'''

  macro.parse_toplevel(TEST_STUFF)

  return last.List([last.Number(0), last.Number(1), last.Number(2)])
