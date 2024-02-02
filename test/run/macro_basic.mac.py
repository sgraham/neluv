import last

def test(macro):
  x = '1+f()'
  expr = macro.parse_expr(x)
  onto = expr.chain
  for a in macro.args:
    onto.append(last.Op('+'))
    onto.append(a)
  return expr
