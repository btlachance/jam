import core
from main import main
from rpython.rlib import jit
from rpython.rlib.objectmodel import we_are_translated

def entry_point(argv):
  # Pycket's params
  jit.set_param(None, 'trace_limit', 1000000)
  jit.set_param(None, 'threshold', 131)
  jit.set_param(None, 'trace_eagerness', 50)
  jit.set_param(None, 'max_unroll_loops', 15)

  # HT pyrolog
  for i in range(len(argv)):
    if argv[i] == '--jit':
      if len(argv) == i + 1:
        print 'missing argument after --jit'
        return 2
      jitarg = argv[i + 1]
      del argv[i:i+2]
      jit.set_user_param(None, jitarg)
      break
  if len(argv) > 1:
    print 'too many arguments'


  if we_are_translated():
    from rpython.rlib import streamio
    from pycket import pycket_json
    stdin = streamio.fdopen_as_stream(0, "r")
    json = pycket_json.loads(stdin.readall())
    return main(core.json_to_term(json))

  else:
    import sys, json
    import pycket_json_adapter as pja
    adapted = pja.adapt(json.load(sys.stdin))
    sys.exit(main(core.json_to_term(adapted)))

def target(driver, args):
  import os
  driver.exe_name = os.getenv('JAM_BINARY_NAME', 'jam-interpreter')
  return entry_point, None

if __name__ == '__main__':
  import sys, os
  if not "JAM_TEST" in os.environ:
    entry_point(sys.argv)
