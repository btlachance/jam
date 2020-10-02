# Clunky, but this must come before other rlib imports so that the
# loggers get patched before relevant instances are made; Only has an
# effect when running the untranslated .py code with python/pypy
import os
import rpython.tool.ansi_print as ap
if 'JAM_QUIET_RPYTHON' in os.environ:
  if hasattr(ap, 'AnsiLog') and hasattr(ap, 'ansi_log'):
    # Older versions of PyPy logged using the AnsiLog class and
    # py.log, so we patch both of them (e.g. mandlebrot stuff would go
    # through AnsiLog, and calling the platform compiler would go
    # through py.log)
    import py
    class QuietAnsiLog(ap.AnsiLog):
      def __init__(self, kw_to_color={}, file=None):
        file = open(os.devnull, 'w')
        ap.AnsiLog.__init__(self, kw_to_color=kw_to_color, file=file)
        ap.ansi_log = QuietAnsiLog()
        ap.AnsiLog = QuietAnsiLog

    class QuietProducer(py.log.Producer):
      def __call__(self, *args):
        pass
    py.log.Producer = QuietProducer

import time
import pytest
import math
from rpython.rlib import jit
from rpython.rlib.objectmodel import we_are_translated, specialize

def bail(s):
  raise JamError(s)

@specialize.call_location()
def subclass_responsibility0(self):
  bail("internal: Subclass responsibility")

@specialize.call_location()
def subclass_responsibility1(self, v):
  bail("internal: Subclass responsibility")

@specialize.call_location()
def subclass_responsibility2(self, v, w):
  bail("internal: Subclass responsibility")

class W_Term(object):
  _immutable_fields_ = ['static', '_can_enter', '_can_enter_return',
                        'surrounding_lambda']

  def is_nil(self):
    return False
  def is_pair(self):
    return False
  def is_symbol(self):
    return False
  def is_integer(self):
    return False
  def is_real(self):
    return False
  def is_boolean(self):
    return False
  def is_none(self):
    return False
  def is_cell(self):
    return False
  def is_string(self):
    return False

  to_string = subclass_responsibility0

  def __init__(self):
    self.static = False
    self._can_enter = False
    self._can_enter_return = False

  def __nonzero__(self):
    return True
  def __len__(self):
    bail("internal: Can't take the length of a non-TermList")
  def __iter__(self):
    bail("internal: Can't iterate a non-TermList")

  atoms_equal = subclass_responsibility1
  def equals_same(self, t):
    bail("internal: Doesn't participate in the atoms_equal protocol")

  def equals_nil(self, o):
    return self.is_nil() and o.equals_same(self)
  def equals_integer(self, n):
    return self.is_integer() and n.equals_same(self)
  def equals_real(self, n):
    return self.is_real() and n.equals_same(self)
  def equals_symbol(self, s):
    return self.is_symbol() and s.equals_same(self)
  def equals_boolean(self, b):
    return self.is_boolean() and b.equals_same(self)
  def equals_string(self, s):
    return self.is_string() and s.equals_same(self)

  def int_value(self):
    bail("internal: Not an integer")
  def real_value(self):
    bail("internal: Not a real")
  def sym_value(self):
    bail("internal: Not a symbol")
  def bool_value(self):
    bail("internal: Not a boolean")
  def cell_value(self):
    bail("internal: Not a cell")
  def string_value(self):
    bail("internal: Not a string")
  def mutate_cell(self, v):
    bail("internal: Not a cell")
  def hd(self):
    bail("internal: Not a pair")
  def tl(self):
    bail("internal: Not a pair")

  def mark_static(self):
    self.static = True
  def can_enter(self):
    if self._can_enter:
      assert not self._can_enter_return
    return self.static and self._can_enter
  def can_enter_return(self):
    if self._can_enter_return:
      assert not self._can_enter
    return self.static and self._can_enter_return
  def to_toplevel_string(self):
    return self.to_string()

  def set_should_enter(self):
    if not self._can_enter:
      self._can_enter = True
  def enable_jitting(self):
    pass
  def get_next_executed_ast(self):
    pass
  def is_lambda(self):
    return False
  def lambda_body0(self):
    return make_none()
  surrounding_lambda = None

class W_ReturnLoopHeader(W_Term):
  _immutable_fields_ = ['term']
  def __init__(self, term):
    W_Term.__init__(self)
    self.term = term
    self.surrounding_lambda = term.surrounding_lambda
  def get_next_executed_ast(self):
    return self
  def set_should_enter(self):
    t = self.term
    if not t._can_enter_return:
      t._can_enter_return = True

def test_responsibility():
  with pytest.raises(JamError):
    W_Term().to_string()

class W_Nil(W_Term):
  def is_nil(self):
    return True
  def atoms_equal(self, other):
    return other.equals_nil(self)
  def equals_same(self, t):
    return True
  def to_string(self):
    return "()"

class W_None(W_Term):
  def is_none(self):
    return True
  def to_string(self):
    return "#%none"
  def atoms_equal(self, other):
    return False
  def mark_static(self):
    pass
W_None.instance = W_None()

def test_none():
  none = make_none()
  assert none.to_string()
  assert none.to_toplevel_string()
  assert none is make_none()
  assert not none.can_enter()
  assert not none.static

class W_Pair(W_Term):
  _immutable_fields_ = ['head', 'tail']

  def __init__(self, hd, tl):
    W_Term.__init__(self)
    self.head = hd
    self.tail = tl
  def is_pair(self):
    return True
  def atoms_equal(self, other):
    return False
  def hd(self):
    return self.head
  def tl(self):
    return self.tail

  def mark_static(self):
    self.head.mark_static()
    self.tail.mark_static()
    if self.head.static and self.tail.static:
      W_Term.mark_static(self)

  def to_string(self):
    return "(%s %s)" % (self.head.to_string(), self.tail.to_string())
  def to_toplevel_string(self):
    subs = [t.to_toplevel_string() for t in W_TermList(self)]
    return "(%s)" % ' '.join(subs)

  def is_lambda(self):
    return self.head.atoms_equal(make_symbol("lambda"))
  def lambda_body0(self):
    after_ordinary_args = self.tail.tl()
    if after_ordinary_args.hd().hd().atoms_equal(make_symbol("dot")):
      return after_ordinary_args.tl().hd()
    else:
      return after_ordinary_args.hd()

  def enable_jitting(self):
    if self.is_lambda():
      self.lambda_body0().set_should_enter()

class W_Symbol(W_Term):
  _immutable_fields_ = ['s']

  def __init__(self, s):
    W_Term.__init__(self)
    self.s = s
  def is_symbol(self):
    return True
  def atoms_equal(self, other):
    return other.equals_symbol(self)
  def equals_same(self, other):
    jit.promote(self)
    return self is other
  def sym_value(self):
    return self.s
  def to_string(self):
    return self.sym_value()

def test_symbol_equal():
  sym1str = 'hello'
  sym2str = 'h' + 'lle'[::-1] + 'o'
  assert not sym1str is sym2str

  s1 = make_symbol(sym1str)
  s2 = make_symbol(sym2str)
  s3 = make_symbol('world')

  assert s1.atoms_equal(s2)
  assert s2.atoms_equal(s1)
  assert not s1.atoms_equal(s3)
  assert not s2.atoms_equal(s3)

class W_Integer(W_Term):
  _immutable_fields_ = ['n']
  def __init__(self, n):
    W_Term.__init__(self)
    self.n = n
  def is_integer(self):
    return True
  def atoms_equal(self, other):
    return other.equals_integer(self)
  def equals_same(self, n):
    return self.int_value() == n.int_value()
  def int_value(self):
    return self.n
  def to_string(self):
    return '%s' % self.int_value()

  def add(self, other):
    if not isinstance(other, W_Integer):
      bail("add: not two integers")
    return self.add_same(other)
  def add_same(self, other):
    return W_Integer(self.n + other.n)

  def subtract(self, other):
    if not isinstance(other, W_Integer):
      bail("subtract: not two integers")
    return self.subtract_same(other)
  def subtract_same(self, other):
    return W_Integer(self.n - other.n)

  def multiply(self, other):
    if not isinstance(other, W_Integer):
      bail("multiply: not two integers")
    return self.multiply_same(other)
  def multiply_same(self, other):
    return W_Integer(self.n * other.n)

  def divide(self, other):
    if not isinstance(other, W_Integer):
      bail("divide: not two integers")
    return self.divide_same(other)
  def divide_same(self, other):
    if other.n == 0:
      bail("divide: division by integer 0")
    return W_Integer(self.n / other.n)

  def divmod(self, other):
    if not isinstance(other, W_Integer):
      bail("divmod: not two integers")
    return self.divmod_same(other)
  def divmod_same(self, other):
    if other.n == 0:
      bail("divide: division by integer 0")
    q, r = self.n / other.n, self.n % other.n
    return W_Integer(q), W_Integer(r)

class W_Real(W_Term):
  _immutable_fields_ = ['n']
  def __init__(self, n):
    W_Term.__init__(self)
    self.n = n
  def is_real(self):
    return True
  def atoms_equal(self, other):
    return other.equals_real(self)
  def equals_same(self, n):
    return self.real_value() == n.real_value()
  def real_value(self):
    return self.n
  def to_string(self):
    return '%s' % self.real_value()

  def add(self, other):
    if not isinstance(other, W_Real):
      bail("add: not two reals")
    return self.add_same(other)
  def add_same(self, other):
    return W_Real(self.n + other.n)

  def subtract(self, other):
    if not isinstance(other, W_Real):
      bail("subtract: not two reals")
    return self.subtract_same(other)
  def subtract_same(self, other):
    return W_Real(self.n - other.n)

  def multiply(self, other):
    if not isinstance(other, W_Real):
      bail("multiply: not two reals")
    return self.multiply_same(other)
  def multiply_same(self, other):
    return W_Real(self.n * other.n)

  def divide(self, other):
    if not isinstance(other, W_Real):
      bail("multiply: not two reals")
    return self.divide_same(other)
  def divide_same(self, other):
    if other.n == 0.0:
      bail("divide: division by real 0")
    return W_Real(self.n / other.n)

  def divmod(self, other):
    if not isinstance(other, W_Real):
      bail("divmod: not two reals")
    return self.divmod_same(other)
  def divmod_same(self, other):
    if other.n == 0.0:
      bail("divmod: division by real 0")
    q, r = math.floor(self.n / other.n), math.fmod(self.n, other.n)
    return W_Real(q), W_Real(r)

  def sin(self):
    return W_Real(math.sin(self.n))

@jit.unroll_safe
def integer_add0(t):
  [v1, v2] = [v for v in W_TermList(t)]
  return v1.add(v2)

@jit.unroll_safe
def integer_subtract0(t):
  [v1, v2] = [v for v in W_TermList(t)]
  return v1.subtract(v2)

@jit.unroll_safe
def integer_multiply0(t):
  [v1, v2] = [v for v in W_TermList(t)]
  return v1.multiply(v2)

@jit.unroll_safe
def integer_divide(t):
  [v1, v2] = [v for v in W_TermList(t)]
  return v1.divide(v2)

@jit.unroll_safe
def integer_divmod(t):
  [v1, v2] = [v for v in W_TermList(t)]
  q, r = v1.divmod(v2)
  return term_list([q, r])

@jit.unroll_safe
def integer_equal(t):
  [v1, v2] = [v for v in W_TermList(t)]
  return make_boolean(v1.atoms_equal(v2))

@jit.unroll_safe
def integer_lt(t):
  [v1, v2] = [v for v in W_TermList(t)]
  return make_boolean(v1.int_value() < v2.int_value())

@jit.unroll_safe
def real_add(t):
  [v1, v2] = [v for v in W_TermList(t)]
  return v1.add(v2)

@jit.unroll_safe
def real_subtract(t):
  [v1, v2] = [v for v in W_TermList(t)]
  return v1.subtract(v2)

@jit.unroll_safe
def real_multiply(t):
  [v1, v2] = [v for v in W_TermList(t)]
  return v1.multiply(v2)

@jit.unroll_safe
def real_divide(t):
  [v1, v2] = [v for v in W_TermList(t)]
  return v1.divide(v2)

@jit.unroll_safe
def real_divmod(t):
  [v1, v2] = [v for v in W_TermList(t)]
  q, r = v1.divmod(v2)
  return term_list([q, r])

@jit.unroll_safe
def real_equal(t):
  [v1, v2] = [v for v in W_TermList(t)]
  return make_boolean(v1.atoms_equal(v2))

@jit.unroll_safe
def real_lt(t):
  [v1, v2] = [v for v in W_TermList(t)]
  return make_boolean(v1.real_value() < v2.real_value())

@jit.unroll_safe
def integer_of_real(t):
  [r] = [v for v in W_TermList(t)]
  return make_integer(int(r.real_value()))

@jit.unroll_safe
def real_of_integer(t):
  [i] = [v for v in W_TermList(t)]
  return make_real(float(i.int_value()))

@jit.unroll_safe
def integer_string(t):
  [i] = [v for v in W_TermList(t)]
  return make_string(i.to_toplevel_string())

@jit.unroll_safe
def real_string(t):
  [r] = [v for v in W_TermList(t)]
  return make_string(r.to_toplevel_string())

@jit.unroll_safe
def real_sin(t):
  [r] = [v for v in W_TermList(t)]
  return r.sin()

@jit.unroll_safe
def string_append(t):
  [s1, s2] = [x for x in W_TermList(t)]
  return s1.append(s2)

@jit.unroll_safe
def string_length(t):
  [s] = [x for x in W_TermList(t)]
  return make_integer(s.length())

@jit.unroll_safe
def string_equal(t):
  [s1, s2] = [x for x in W_TermList(t)]
  return make_boolean(s1.string_value() == s2.string_value())

class W_Boolean(W_Term):
  _immutable_fields_ = ['b']
  def __init__(self, b):
    W_Term.__init__(self)
    self.b = b
  def is_boolean(self):
    return True
  def atoms_equal(self, other):
    return other.equals_boolean(self)
  def equals_same(self, b):
    return self.bool_value() == b.bool_value()
  def bool_value(self):
    return self.b
  def to_string(self):
    return '#t' if self.bool_value() else '#f'

class W_Cell(W_Term):
  _immutable_fields_ = []
  def __init__(self):
    W_Term.__init__(self)
    self.value = make_none()

  def is_cell(self):
    return True

  def atoms_equal(self, other):
    return False

  def to_string(self):
    return self.value.to_string()

  def cell_value(self):
    return self.value

  def mutate_cell(self, v):
    self.value = v

class W_String(W_Term):
  _immutable_fields_ = ['s']
  def __init__(self, s):
    W_Term.__init__(self)
    self.s = s

  def is_string(self):
    return True
  def atoms_equal(self, other):
    return other.equals_string(self)
  def equals_same(self, s):
    return self.string_value() == s.string_value()
  def string_value(self):
    return self.s
  def to_string(self):
    return self.s
  def to_toplevel_string(self):
    if we_are_translated():
      # HT Pycket
      from pypy.objspace.std.bytesobject import string_escape_encode
      return string_escape_encode(self.s, '"')
    else:
      return '"%s"' % self.s.encode('string_escape')

  def append(self, other):
    return W_String(self.s + other.string_value())

  def length(self):
    return len(self.s)

def test_string():
  s0 = make_string("fish")
  s1 = make_string("chips")
  x = make_integer(0)

  assert not x.is_string()
  assert s0.is_string()
  assert s0.atoms_equal(s0)
  assert s0.atoms_equal(make_string("fish"))

  assert s0.append(s1).string_value() == "fishchips"
  assert not s0.atoms_equal(s1)

class W_TermList(W_Term):
  _immutable_fields_ = ['t']

  def __init__(self, termlist):
    W_Term.__init__(self)
    self.t = termlist
  def is_nil(self):
    return self.t.is_nil()
  def is_pair(self):
    return self.t.is_pair()
  def is_symbol(self):
    return self.t.is_symbol()
  def is_integer(self):
    return self.t.is_integer()
  def is_boolean(self):
    return self.t.is_boolean()
  def is_none(self):
    return self.t.is_none()
  def atoms_equal(self, other):
    return self.t.atoms_equal(other)

  @jit.unroll_safe
  def __iter__(self):
    return W_TermList(self.t)

  def next(self):
    if self.t.is_nil():
      raise StopIteration()
    hd = self.t.hd()
    self.t = self.t.tl()
    return hd

  @jit.unroll_safe
  def __len__(self):
    n = 0
    for t in self:
      n = n + 1
    return n

  def mark_static(self):
    self.t.mark_static()
    if self.t.static:
      W_Term.mark_static(self)

  def to_string(self):
    return self.t.to_string()

def test_W_TermList():
  y = W_TermList(term_list([]))
  assert len(y) == 0

  terms = term_list([make_integer(0), make_integer(1), make_integer(2)])
  assert len(W_TermList(terms)) == 3
  for x in W_TermList(terms):
    pass
  assert x.int_value() == 2

def make_nil():
  return W_Nil()

def make_none():
  return W_None.instance

def make_pair(hd, tl):
  return W_Pair(hd, tl)

SymbolCache = { }
@jit.elidable
def make_symbol(s):
  sym = SymbolCache.get(s, None)
  if sym is None:
    sym = W_Symbol(s)
    SymbolCache[s] = sym
  return sym

FormalsCache = { }
@jit.elidable
def make_formals(formals_str):
  formals = FormalsCache.get(formals_str, None)
  if formals is None:
    formals = term_list([make_symbol(s) for s in formals_str.split(formals_sep)])
    FormalsCache[formals_str] = formals
  return formals
formals_sep = "\0"

def make_integer(n):
  return W_Integer(n)

def make_real(n):
  return W_Real(n)

def make_string(s):
  return W_String(s)

def make_boolean(b):
  return W_Boolean(b)

def make_cell():
  return W_Cell()

@jit.unroll_safe
def term_list(vs):
  result = make_nil()
  for v in reversed(vs):
    result = make_pair(v, result)
  return result

def get_hd(t):
  return t.hd()

def get_tl(t):
  return t.tl()

def atoms_equal(x, y):
  return x.atoms_equal(y)

def is_nil(t):
  return t.is_nil()

def is_pair(t):
  return t.is_pair()

def is_symbol(t):
  return t.is_symbol()

def is_integer(t):
  return t.is_integer()

def is_real(t):
  return t.is_real()

def is_string(t):
  return t.is_string()

def is_boolean(t):
  return t.is_boolean()

def is_none(t):
  return t.is_none()

def is_list(t):
  if t.is_nil():
    return True
  if t.is_pair():
    return True
  return False

def print_term(t):
  print t.to_toplevel_string()

def all_terms(pred, terms):
  if terms.is_nil():
    return True
  if terms.is_pair():
    hd = terms.hd()
    return pred(hd)
  return False

@jit.unroll_safe
def map_terms(f, terms):
  mapped = []
  for term in W_TermList(terms):
    mapped.append(f(term))
  return term_list(mapped)

# I can't specialize against the second argument; RPython seems to
# think the next() method of the iterator's I pass to this (W_TermList
# iterators) have as many arguments as izip2. Or something like
# that. When I specialize against argtype 1 (or argtype 0,1) there's a
# list index out of range error in function specialize_argtype in
# rpython.annotator.specialize; it tries to get args_s[1] for the next
# method, which is bogus. I only have a few callsites to izip2, so
# specializing the function to each one should be fine...
@jit.unroll_safe
@specialize.call_location() 
def izip2(xs, ys):
  ixs, iys = iter(xs), iter(ys)
  while True:
    yield (next(ixs), next(iys))

def test_izip2():
  ns = [1, 2, 3]
  ts = [make_symbol("a"), make_symbol("b"), make_symbol("c")]

  count = 0
  for _ in izip2([], []):
    count += 1
  assert count == 0

  count = 0
  for _ in izip2(ns, ts):
    count += 1
  assert count == 3

# INV: levels contains at least one non-atomic level
@jit.unroll_safe
def decompose_values(levels, terms):
  levels = [v.int_value() for v in W_TermList(levels)]
  terms = [t for t in W_TermList(terms)]
  if not equal_lengths(levels, terms):
    bail("Ellipses used on unequal-length lists")
  decomposed = []
  while not stop_now(levels, terms):
    current_decomp = []
    remaining_terms = []
    for level, term in izip2(levels, terms):
      if level == 0:
        current_decomp.append(term)
        remaining_terms.append(term)
      else:
        current_decomp.append(term.hd())
        remaining_terms.append(term.tl())
    decomposed.append(term_list(current_decomp))
    terms = remaining_terms
  return term_list(decomposed)

def test_decompose_values():
  make_int = make_integer
  levels = term_list([make_int(0), make_int(1), make_int(0)])
  terms = term_list([make_symbol("a"), term_list([make_int(3), make_int(4)]), make_symbol("b")])

  decomposed = W_TermList(decompose_values(levels, terms))
  assert len(decomposed) == 2

  for x in decomposed:
    assert x.hd().sym_value() == "a"
    assert (x.tl().hd().int_value() == 3
            or x.tl().hd().int_value() == 4)
    assert x.tl().tl().hd().sym_value() == "b"

  with pytest.raises(JamError):
    levels = term_list([make_int(1), make_int(1)])
    terms = term_list([term_list([make_int(n) for n in range(1)]),
                       term_list([make_int(n) for n in range(2)])])
    decompose_values(levels, terms)

# INV: levels contains at least one non-atomic level
@jit.unroll_safe
def equal_lengths(levels, terms):
  length = -1
  for level, term in izip2(levels, terms):
    if level == 0:
      continue
    term = W_TermList(term)
    if length == -1:
      length = len(term)
      continue
    if length != len(term):
      return False
  return length != -1

def test_equal_lengths():
  terms = [make_integer(0), term_list([make_symbol("s"), make_symbol("x")])]
  levels = [0, 1]
  assert equal_lengths(levels, terms)

@jit.unroll_safe
def stop_now(levels, terms):
  for level, term in izip2(levels, terms):
    if level == 0:
      continue
    return term.is_nil()
  bail("internal: stop_now needs at least one non-atomic term")

def error():
  bail("Error raised (did pattern matching fail")

class ExnTestFailure(Exception):
  def __init__(self, s, w):
    self.message = s
    self.witness = w
  pass

def fail_test(s, wit):
  if wit.is_none():
    wit = None
  raise ExnTestFailure(s, wit)

class ExnTestSuccess(Exception):
  pass

def pass_test():
  raise ExnTestSuccess()

def json_to_term(v):
  if v.is_null:
    return make_nil()
  if not v.is_object:
    bail("non-null json was not an object")
  obj = v.value_object()
  if "integer" in obj:
    tmp_i = obj.get("integer", None)
    if not (tmp_i and tmp_i.is_int):
      bail("internal: integer json didn't contain an int")
    return make_integer(tmp_i.value_int())
  if "real" in obj:
    tmp_d = obj.get("real", None)
    if not (tmp_d and tmp_d.is_float):
      bail("internal: real json didn't contain a float")
    return make_real(tmp_d.value_float())
  if "string" in obj:
    tmp_s = obj.get("string", None)
    if not (tmp_s and tmp_s.is_string):
      bail("internal: string json didn't contain a string")
    return make_string(tmp_s.value_string())
  if "symbol" in obj:
    tmp_s = obj.get("symbol", None)
    if not(tmp_s and tmp_s.is_string):
      bail("internal: symbol json didn't contain a string")
    return make_symbol(tmp_s.value_string())
  if "pair" in obj:
    tmp_p = obj.get("pair", None)
    if not(tmp_p and tmp_p.is_array):
      bail("internal: pair json didn't contain an array")
    [hd, tl] = tmp_p.value_array()
    return make_pair(json_to_term(hd), json_to_term(tl))
  if "boolean" in obj:
    tmp_b = obj.get("boolean", None)
    if not(tmp_b and tmp_b.is_bool):
      bail("internal: boolean json didn't contain a bool")

    # Not sure how to compare with the singletons json_true/json_false
    # when the object might be an instance of the Adapter from
    # pycket_json_adapter... so I think this is the best we can do
    return make_boolean(tmp_b.tostring() == "true")
  bail("internal: couldn't make a term from json")

def string_to_term(s):
  if we_are_translated():
    from pycket import pycket_json
    json = pycket_json.loads(s)
    return json_to_term(json)
  else:
    import json
    import pycket_json_adapter as pja
    adapted = pja.adapt(json.loads(s))
    return json_to_term(adapted)

# XXX I think I can change the linked environment representation to
# look like something Pycket's, which will reduce the number of guards
# in traces of variable lookup. Pycket can do this because it stores
# the static scope information separate from the environment. So, for
#
#     (let ([x #t] [z #f] [a #t])
#       (let ([y #f] [w #f])
#         e)))
#
# imagine the environment for e, call it env0, has the values of y and
# w directly in it, and env0 has a link to another environment, env1,
# that has values of x z and a directly in it. What I'm calling the
# static scope information looks like
#
#    '(([y 0] [w 1])
#      ([x 0] [z 1] [a 2]))
#
# We can compute that entire static scope chain based off of how the
# environment is extended, and we can use a cache to make sure that
# it's constant.
#
# Treating the entire chain as one constant helps because then when we
# lookup we just incur the cost of one guard on the particular
# chain. Lookup now tells us how many links to traverse and, once
# we've traversed those links, the offset of the value into the
# environment's list of values.
#
# Before, lookup just looked at the current environment's list of
# variables and told us whether a variable was bound in the current
# environment. And we specialized the lookup against the list of
# variables.  If the variable wasn't found, lookup traversed the
# environment's link and recurred on that environment. Since each
# lookup specializes against the list of variables, and we examined a
# list of variable for each environment lookup consulted, there was a
# guard for each list of variables.
#
# There's still a cost to traversing the links, but that is the price
# we pay for environments with sharing. That cost can probably be made
# worst-case logarithmic instead of linear in the number of links but
# I haven't looked into that yet.
class W_Environment(W_Term):
  def is_nil(self):
    return False
  def is_pair(self):
    return False
  def is_symbol(self):
    return False
  def is_integer(self):
    return False
  def is_boolean(self):
    return False
  def atoms_equal(self, other):
    return False
  def to_string(self):
    return "#%env"
  def mark_static(self):
    pass
  def lookup_raw(self, y):
    bail("Variable %s not bound to a cell" % y.to_string())

  lookup = subclass_responsibility1
  is_bound = subclass_responsibility1

class W_EmptyEnvironment(W_Environment):
  def lookup(self, y):
    bail("Varaible %s not bound" % y.to_string())
  def is_bound(self, y):
    return False

class W_SingleEnvironment(W_Environment):
  def __init__(self, x, v, env):
    W_Environment.__init__(self)
    self.x = x
    self.v = v
    self.env = env
  def lookup(self, y):
    if self.x.atoms_equal(y):
      return self.v
    return self.env.lookup(y)
  def is_bound(self, y):
    if self.x.atoms_equal(y):
      return True
    return self.env.is_bound(y)

class W_MultipleEnvironment(W_Environment):
  _immutable_fields_ = ['xs', 'vs[*]', 'env']

  @jit.unroll_safe
  def __init__(self, xs, vs, env):
    W_Environment.__init__(self)
    self.xs = xs
    self.vs = [v for v in W_TermList(vs)]
    self.env = env

  @jit.unroll_safe
  def lookup(self, y):
    xs = jit.promote(self.xs)
    index, at = -1, 0

    for x in W_TermList(xs):
      if x.atoms_equal(y):
        index = at
        break
      at = at + 1

    if index == -1:
      return self.env.lookup(y)
    else:
      return self.vs[index]

  @jit.unroll_safe
  def is_bound(self, y):
    xs = jit.promote(self.xs)

    for x in W_TermList(xs):
      if x.atoms_equal(y):
        return True
    return self.env.is_bound(y)

def test_env():
  empty = W_EmptyEnvironment()
  x, y = make_symbol('x'), make_symbol('y')
  xs0 = term_list([x, y])
  vs0 = term_list([make_integer(0), make_integer(1)])
  env0 = W_MultipleEnvironment(xs0, vs0, empty)

  assert not empty.is_bound(x)
  assert env0.is_bound(y)
  assert not env0.is_bound(make_symbol('z'))
  assert env0.lookup(x).int_value() == 0
  assert env0.lookup(y).int_value() == 1

class W_MultipleEnvironmentDynamic(W_Environment):
  @jit.unroll_safe
  def __init__(self, xs, vs, env):
    W_Environment.__init__(self)
    indices = {}
    for x, i in izip2(W_TermList(xs), range(len(W_TermList(xs)))):
      indices[x] = i
    self.indices = indices
    self.vs = [v for v in W_TermList(vs)]
    self.env = env

  def lookup(self, y):
    i = self.indices.get(y, -1)
    if i != -1:
      return self.vs[i]
    return self.env.lookup(y)

  def is_bound(self, y):
    return y in self.indices

def test_envdynamic():
  empty = W_EmptyEnvironment()

  x, y = make_symbol('x'), make_symbol('y')
  xs0 = term_list([x, y])
  vs0 = term_list([make_integer(0), make_integer(1)])
  env0 = W_MultipleEnvironmentDynamic(xs0, vs0, empty)

  assert not empty.is_bound(x)
  assert env0.is_bound(y)
  assert not env0.is_bound(make_symbol('z'))
  assert env0.lookup(x).int_value() == 0
  assert env0.lookup(y).int_value() == 1

def is_environment(v):
  return isinstance(v, W_Environment)

def test_envwrongnumber():
  empty = W_EmptyEnvironment()
  x, y = make_symbol('x'), make_symbol('y')
  v, w = make_integer(0), make_integer(1)

  xs0 = term_list([x, y])
  vs0 = term_list([v])

  xs1 = term_list([x])
  vs1 = term_list([v, w])

  with pytest.raises(JamError):
    environment_extend(term_list([empty, xs0, vs0]))

  with pytest.raises(JamError):
    environment_extend(term_list([empty, xs1, vs1]))

class W_CellEnvironment(W_MultipleEnvironment):
  def lookup(self, y):
    v = self.lookup_raw(y)
    if v.is_cell():
      return v.cell_value()
    else:
      return v

  def lookup_raw(self, y):
    return W_MultipleEnvironment.lookup(self, y)

def test_envcells():
  empty = W_EmptyEnvironment()
  x, y = make_symbol('x'), make_symbol('y')
  xs = term_list([x, y])

  env = environment_extend_cells(term_list([empty, xs]))
  assert env.is_bound(x)
  assert env.lookup(x).is_none()
  assert env.is_bound(y)
  assert env.lookup(y).is_none()
  assert not env.is_bound(make_symbol('z'))

  environment_set_cells(term_list([env, xs, term_list([env, env])]))
  assert env.lookup(x) is env
  assert env.lookup(y) is env

@jit.unroll_safe
def environment_lookup(t):
  [env, x] = [x for x in W_TermList(t)]
  return env.lookup(x)

@jit.unroll_safe
def environment_is_bound(t):
  [env, x] = [x for x in W_TermList(t)]
  return make_boolean(env.is_bound(x))

@jit.unroll_safe
def environment_extend1(t):
  [env, x, v] = [x for x in W_TermList(t)]
  return W_SingleEnvironment(x, v, env)

@jit.unroll_safe
def environment_extend(t):
  [env, xs, vs] = [x for x in W_TermList(t)]
  if not len(W_TermList(xs)) == len(W_TermList(vs)):
    bail("can't extend environment with two lists of unequal length")

  if xs.static:
    formals = xs
  else:
    formals_str = formals_sep.join([x.sym_value() for x in W_TermList(xs)])
    jit.promote_string(formals_str)
    formals = make_formals(formals_str)

  return W_MultipleEnvironment(formals, vs, env)

@jit.unroll_safe
def environment_empty(t):
  [] = [x for x in W_TermList(t)]
  return W_EmptyEnvironment()

def test_env_metafunction():
  empty = W_EmptyEnvironment()
  x, y = make_symbol('x'), make_symbol('y')
  xs0 = term_list([x, y])
  vs0 = term_list([make_integer(4), make_integer(3)])

  env0 = environment_extend(term_list([empty, xs0, vs0]))
  assert env0.lookup(y).int_value() == 3
  assert env0.lookup(x).int_value() == 4

@jit.unroll_safe
def environment_extend_cells(t):
  [env, xs] = [x for x in W_TermList(t)]
  vs = term_list([make_cell() for x in W_TermList(xs)])
  return W_CellEnvironment(xs, vs, env)

@jit.unroll_safe
def environment_set_cells(t):
  [env, xs, vs] = [x for x in W_TermList(t)]

  for x, v in izip2(W_TermList(xs), W_TermList(vs)):
    cell = env.lookup_raw(x)
    if not cell.is_cell():
      bail("internal: environment_set_cells got a non-cell for variable %s" %
           x.to_string())

    cell.mutate_cell(v)

  return make_nil()

class JamDone(Exception):
  def __init__(self, v):
    self.v = v

class JamError(Exception):
  def __init__(self, s):
    self.s = s

def done(v):
  raise JamDone(v)

@jit.unroll_safe
def list_reverse(t):
  [args] = [x for x in W_TermList(t)]
  args = [x for x in W_TermList(args)]
  args.reverse()
  return term_list(args)

@jit.unroll_safe
def list_append(t):
  [xs, ys] = [x for x in W_TermList(t)]

  if xs.is_nil():
    return ys

  xs = [x for x in W_TermList(xs)]
  xs.reverse()
  for x in xs:
    ys = make_pair(x, ys)
  return ys

def clock_milliseconds(t):
  [] = [x for x in W_TermList(t)]
  return make_integer(int(time.clock() * 1000))

class W_Sequence(W_Term):
  elements = subclass_responsibility0
  set = subclass_responsibility2

  def atoms_equal(self, other):
    return False
  def to_string(self):
    return "#%sequence"
  def length(self):
    return len(self.elements())
  def element_at(self, i):
    return self.elements()[i]

class W_MutableSequence(W_Sequence):
  def __init__(self, xs):
    W_Sequence.__init__(self)
    self.xs = xs
  def elements(self):
    return self.xs
  def set(self, i, x):
    self.xs[i] = x
class W_ImmutableSequence(W_Sequence):
  _immutable_fields_ = ['xs[*]']
  def __init__(self, xs):
    W_Sequence.__init__(self)
    self.xs = xs[:]
  def elements(self):
    return self.xs
  def set(self, i, x):
    bail("set only works on mutable sequences; got an immutable sequence")

def mutable_sequence_of(t):
  xs = [x for x in W_TermList(t)]
  return W_MutableSequence(xs)

def immutable_sequence_of(t):
  xs = [x for x in W_TermList(t)]
  return W_ImmutableSequence(xs)

@jit.unroll_safe
def sequence_element_at(t):
  [seq, i] = [x for x in W_TermList(t)]
  return seq.element_at(i.int_value())

@jit.unroll_safe
def sequence_set(t):
  [seq, i, x] = [x for x in W_TermList(t)]
  seq.set(i.int_value(), x)
  return make_nil()

@jit.unroll_safe
def sequence_length(t):
  [seq] = [x for x in W_TermList(t)]
  return make_integer(seq.length())

def is_mutable_sequence(v):
  return isinstance(v, W_MutableSequence)
def is_immutable_sequence(v):
  return isinstance(v, W_ImmutableSequence)

def test_seq():
  mut0 = mutable_sequence_of(make_nil())
  immut0 = immutable_sequence_of(make_nil())
  assert mut0.length() == 0
  assert is_mutable_sequence(mut0)
  assert not(is_mutable_sequence(immut0))
  assert immut0.length() == 0
  assert is_immutable_sequence(immut0)
  assert not(is_immutable_sequence(mut0))

  elems = term_list([make_integer(3), make_integer(5), make_integer(7)])
  mut3 = mutable_sequence_of(elems)
  immut3 = immutable_sequence_of(elems)
  assert mut3.length() == 3
  assert immut3.length() == 3

  assert mut3.element_at(0).int_value() == 3
  assert mut3.element_at(1).int_value() == 5
  assert mut3.element_at(2).int_value() == 7
  mut3.set(1, make_nil())
  assert mut3.element_at(0).int_value() == 3
  assert mut3.element_at(1).is_nil()

  assert immut3.element_at(0).int_value() == 3
  assert immut3.element_at(1).int_value() == 5
  assert immut3.element_at(2).int_value() == 7
  with pytest.raises(JamError):
    immut3.set(1, make_nil)

def is_file(v):
  return isinstance(v, W_File)

class W_File(W_Term):
  def write(self, string):
    self.file.write(string)
  def atoms_equal(self, other):
    return False
  def flush(self):
    self.file.flush()
  def to_string(self):
    return "#%file"

class W_StrictFile(W_File):
  def __init__(self, file):
    W_File.__init__(self)
    self.file = file

class W_LazyFile(W_File):
  def __init__(self, thunk):
    W_File.__init__(self)
    self.thunk = thunk
    self.file = None
  def write(self, string):
    if self.file is None:
      self.file = self.thunk()
    W_File.write(self, string)
  def flush(self):
    if self.file is None:
      self.file = self.thunk()
    W_File.flush(self)

def get_stdout():
  from rpython.rlib import streamio as sio
  return sio.fdopen_as_stream(1, "w", buffering = 1)
def get_stderr():
  from rpython.rlib import streamio as sio
  return sio.fdopen_as_stream(2, "w", buffering = 1)
stdout = W_LazyFile(get_stdout)
stderr = W_LazyFile(get_stderr)

def file_write(t):
  [f, s] = [x for x in W_TermList(t)]
  f.write(s.string_value())
  return make_nil()
def get_stdout(t):
  [] = [x for x in W_TermList(t)]
  return stdout
def get_stderr(t):
  [] = [x for x in W_TermList(t)]
  return stderr

# https://stackoverflow.com/a/35857/168645
def shellquote(s):
  # Originally, this function was just
  #   return "'" + s.replace("'", "'\\''") + "'"
  # But RPython s.replace only works when the replacement is a char
  # and I think what's below is equivalent

  replaced = "'\\''".join(s.split("'"))
  return "'" + replaced + "'"

def systemstar_json_term(t):
  from rpython.rlib import rfile
  args = [shellquote(x.string_value()) for x in W_TermList(t)]
  f = rfile.create_popen_file(' '.join(args), 'r')
  s = f.read()
  f.close()
  return string_to_term(s)

class W_Location(W_Term):
  def __init__(self):
    W_Term.__init__(self)
    self.contents = make_none()
    self.index = -1
  def to_string(self):
    return "#%location"
  def atoms_equal(self, other):
    return False

# I removed the weak list part of this because I was getting
# translation errors. I added stubs for the methods I used from the
# mixin (initialize, add_handle) so that I could try again later.

# class W_Store(W_Term, RWeakListMixin):
# # I'm not certain we want to materialize a collection of the
# # locations but holding weak references to them shouldn't hurt.

class W_Store(W_Term):
  def __init__(self):
    W_Term.__init__(self)
    self.initialize()

  def initialize(self):
    pass
  def add_handle(self, l):
    return 0

  def fresh_location(self):
    return W_Location()
  def extend(self, l, v): # only extend stores w/fresh locations
    assert isinstance(l, W_Location)
    assert l.index == -1
    l.index = self.add_handle(l)
    l.contents = v
  def update_location(self, l, v): # only update existing locations
    assert isinstance(l, W_Location)
    assert l.index != -1
    l.contents = v
  def deref(self, l):
    assert isinstance(l, W_Location)
    return l.contents
  def to_string(self):
    return "#%store"
  def atoms_equal(self, other):
    return False

def is_store(v):
  return isinstance(v, W_Store)
def is_location(v):
  return isinstance(v, W_Location)

def store_empty(t):
  [] = [t for t in W_TermList(t)]
  return W_Store()
@jit.unroll_safe
def store_fresh_location(t):
  [s] = [t for t in W_TermList(t)]
  return s.fresh_location()
@jit.unroll_safe
def store_fresh_distinct_locations(t):
  [s, ts] = [t for t in W_TermList(t)]
  return term_list([s.fresh_location() for t in W_TermList(ts)])
@jit.unroll_safe
def store_extend(t):
  [s, ls, vs] = [t for t in W_TermList(t)]
  ls = [l for l in W_TermList(ls)]
  vs = [v for v in W_TermList(vs)]
  for l, v in izip2(ls, vs):
    s.extend(l, v)
  return make_nil()
@jit.unroll_safe
def store_update_location(t):
  [s, l, v] = [t for t in W_TermList(t)]
  s.update_location(l, v)
  return make_nil()
@jit.unroll_safe
def store_dereference(t):
  [s, l] = [t for t in W_TermList(t)]
  return s.deref(l)
@jit.unroll_safe
def term_set_can_enter(t):
  [term] = [x for x in W_TermList(t)]
  term.set_should_enter()
  return make_nil()
@jit.unroll_safe
def lists_have_same_length(t):
  [xs, ys] = [t for t in W_TermList(t)]
  while not xs.is_nil() and not ys.is_nil():
    xs, ys = xs.tl(), ys.tl()
  return make_boolean(xs.is_nil() and ys.is_nil())

from pycket.callgraph import CallGraph
call_graph = CallGraph()

@jit.unroll_safe
def register_call(t):
  [callsite, callee, return_loop_header] = [x for x in W_TermList(t)]
  return_loop_header = W_ReturnLoopHeader(return_loop_header)
  call_graph.register_call(callee, callsite, return_loop_header, None)
  return make_nil()

def set_surrounding_lambda(t, current_lam=None):
  t.surrounding_lambda = current_lam

  if t.is_pair():
    head = t.hd()
    tail = t.tl()
    if t.is_lambda():
      current_lam = t

    # Sloppy since this sets surrounding_lambda to every subterm,
    # e.g. the arg list, to the current lambda. But it should be fine.
    set_surrounding_lambda(head, current_lam)
    set_surrounding_lambda(tail, current_lam)

if __name__ == "__test__":
  pytest.main([__file__, "-q"])

if __name__ == "__main__":
  import os
  if "JAM_TEST" in os.environ:
    import runpy
    runpy.run_path(__file__, None, "__test__")
