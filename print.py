import sys

def print(cctx, args, block):
  __builtins__['print']('HAI', args, file=sys.stderr)
  __builtins__['print'](cctx)
  return 'MACRO x'
