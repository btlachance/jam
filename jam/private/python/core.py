import pytest
from rpython.rlib import jit
from rpython.rlib.objectmodel import we_are_translated, specialize

def bail(s):
  raise JamError(s)

@specialize.call_location()
def subclass_responsibility0(self):
  assert False, "internal: Subclass responsibility"

@specialize.call_location()
def subclass_responsibility1(self, v):
  assert False, "internal: Subclass responsibility"

class W_Term(object):
  _immutable_fields_ = ['static']

  is_nil = subclass_responsibility0
  is_pair = subclass_responsibility0
  is_symbol = subclass_responsibility0
  is_integer = subclass_responsibility0
  is_boolean = subclass_responsibility0
  is_none = subclass_responsibility0
  to_string = subclass_responsibility0

  def __init__(self):
    self.static = False

  def __nonzero__(self):
    return True
  def __len__(self):
    assert False, "internal: Can't take the length of a non-TermList"
  def __iter__(self):
    assert False, "internal: Can't iterate a non-TermList"

  atoms_equal = subclass_responsibility1
  def equals_same(self, t):
    assert False, "internal: Doesn't participate in the atoms_equal protocol"

  def equals_nil(self, o):
    return self.is_nil() and o.equals_same(self)
  def equals_integer(self, n):
    return self.is_integer() and n.equals_same(self)
  def equals_symbol(self, s):
    return self.is_symbol() and s.equals_same(self)
  def equals_boolean(self, b):
    return self.is_boolean() and b.equals_same(self)

  def int_value(self):
    assert False, "internal: Not an integer"
  def sym_value(self):
    assert False, "internal: Not a symbol"
  def bool_value(self):
    assert False, "internal: Not a boolean"
  def hd(self):
    assert False, "internal: Not a pair"
  def tl(self):
    assert False, "internal: Not a pair"

  def mark_static(self):
    self.static = True
  def can_enter(self):
    return self.static
  def to_toplevel_string(self):
    return self.to_string()

def test_responsibility():
  with pytest.raises(AssertionError):
    W_Term().is_nil()

class W_Nil(W_Term):
  def is_nil(self):
    return True
  def is_pair(self):
    return False
  def is_symbol(self):
    return False
  def is_integer(self):
    return False
  def is_boolean(self):
    return False
  def is_none(self):
    return False
  def atoms_equal(self, other):
    return other.equals_nil(self)
  def equals_same(self, t):
    return True
  def to_string(self):
    return "()"

class W_None(W_Term):
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
  def is_nil(self):
    return False
  def is_pair(self):
    return True
  def is_symbol(self):
    return False
  def is_integer(self):
    return False
  def is_boolean(self):
    return False
  def is_none(self):
    return False
  def atoms_equal(self, other):
    return False
  def hd(self):
    return self.head
  def tl(self):
    return self.tail

  def mark_static(self):
    W_Term.mark_static(self)
    self.head.mark_static()
    self.tail.mark_static()

  def to_string(self):
    return "(%s %s)" % (self.head.to_string(), self.tail.to_string())
  def to_toplevel_string(self):
    subs = [t.to_toplevel_string() for t in W_TermList(self)]
    return "(%s)" % ' '.join(subs)

class W_Symbol(W_Term):
  _immutable_fields_ = ['s']

  def __init__(self, s):
    W_Term.__init__(self)
    self.s = s
  def is_nil(self):
    return False
  def is_pair(self):
    return False
  def is_symbol(self):
    return True
  def is_integer(self):
    return False
  def is_boolean(self):
    return False
  def is_none(self):
    return False
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
  def is_nil(self):
    return False
  def is_pair(self):
    return False
  def is_symbol(self):
    return False
  def is_integer(self):
    return True
  def is_boolean(self):
    return False
  def is_none(self):
    return False
  def atoms_equal(self, other):
    return other.equals_integer(self)
  def equals_same(self, n):
    return self.int_value() == n.int_value()
  def int_value(self):
    return self.n
  def to_string(self):
    return '%s' % self.int_value()

  def add(self, other):
    assert isinstance(other, W_Integer)
    return self.add_same(other)
  def add_same(self, other):
    return W_Integer(self.n + other.n)

  def subtract(self, other):
    assert isinstance(other, W_Integer)
    return self.subtract_same(other)
  def subtract_same(self, other):
    return W_Integer(self.n - other.n)

  def multiply(self, other):
    assert isinstance(other, W_Integer)
    return self.multiply_same(other)
  def multiply_same(self, other):
    return W_Integer(self.n * other.n)

def integer_add0(t):
  [v1, v2] = [v for v in W_TermList(t)]
  return v1.add(v2)

def integer_subtract0(t):
  [v1, v2] = [v for v in W_TermList(t)]
  return v1.subtract(v2)

def integer_multiply0(t):
  [v1, v2] = [v for v in W_TermList(t)]
  return v1.multiply(v2)

class W_Boolean(W_Term):
  _immutable_fields_ = ['b']
  def __init__(self, b):
    W_Term.__init__(self)
    self.b = b
  def is_nil(self):
    return False
  def is_pair(self):
    return False
  def is_symbol(self):
    return False
  def is_integer(self):
    return False
  def is_boolean(self):
    return True
  def is_none(self):
    return False
  def atoms_equal(self, other):
    return other.equals_boolean(self)
  def equals_same(self, b):
    return self.bool_value() == b.bool_value()
  def bool_value(self):
    return self.b
  def to_string(self):
    return '#t' if self.bool_value() else '#f'

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
    self = self.t
    while not self.is_nil():
      yield self.hd()
      self = self.tl()

  @jit.unroll_safe
  def __len__(self):
    n = 0
    for t in self:
      n = n + 1
    return n

  def mark_static(self):
    W_Term.mark_static(self)
    self.t.mark_static()

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

def make_integer(n):
  return W_Integer(n)

def make_boolean(b):
  return W_Boolean(b)

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

def is_boolean(t):
  return t.is_boolean()

def is_none(t):
  return t.is_none()

def is_list(t):
  if t.is_nil():
    return True
  if t.is_pair():
    t = t.tl()
    while t.is_pair():
      t = t.tl()
    return t.is_nil()
  return False

def print_term(t):
  print t.to_toplevel_string()

def all_terms(pred, terms):
  for term in W_TermList(terms):
    if not pred(term):
      return False
  return True

@jit.unroll_safe
def map_terms(f, terms):
  mapped = []
  for term in W_TermList(terms):
    mapped.append(f(term))
  return term_list(mapped)

# XXX RPython balks when I specialize at 0,1 but since the args end up being
# the same type for both of my calls to this then it's apparently sufficinet
# to specialize on the type of xs
@specialize.argtype(0)
@jit.unroll_safe
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
  assert equal_lengths(levels, terms), "Ellipses used on unequal-length lists"
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


# INV: levels contains at least one non-atomic level
def equal_lengths(levels, terms):
  length = -1
  for level, term in izip2(levels, terms):
    if level == 0:
      continue
    term = W_TermList(term)
    if length == -1:
      length = len(term)
    else:
      continue
    if length != len(term):
      return False
  return length != -1

def test_equal_lengths():
  terms = [make_integer(0), term_list([make_symbol("s"), make_symbol("x")])]
  levels = [0, 1]
  assert equal_lengths(levels, terms)

def stop_now(levels, terms):
  for level, term in izip2(levels, terms):
    if level == 0:
      continue
    return term.is_nil()
  assert False, "internal: stop_now needs at least one non-atomic term"

def error():
  assert False, "Error raised (did pattern matching fail"

class ExnTestFailure(Exception):
  def __init__(self, s):
    self.message = s
  pass

def fail_test(s):
  raise ExnTestFailure(s)

class ExnTestSuccess(Exception):
  pass

def pass_test():
  raise ExnTestSuccess()

def json_to_term(v):
  if v.is_null:
    return make_nil()
  assert v.is_object
  obj = v.value_object()
  if "integer" in obj:
    tmp_i = obj.get("integer", None)
    assert tmp_i and tmp_i.is_int, "internal: integer json didn't contain an int"
    return make_integer(tmp_i.value_int())
  if "symbol" in obj:
    tmp_s = obj.get("symbol", None)
    assert tmp_s and tmp_s.is_string, "internal: symbol json didn't contain a string"
    return make_symbol(tmp_s.value_string())
  if "pair" in obj:
    tmp_p = obj.get("pair", None)
    assert tmp_p and tmp_p.is_array, "internal: pair json didn't contain an array"
    [hd, tl] = tmp_p.value_array()
    return make_pair(json_to_term(hd), json_to_term(tl))
  if "boolean" in obj:
    tmp_b = obj.get("boolean", None)
    assert tmp_b and tmp_b.is_bool, "internal: boolean json didn't contain a bool"

    # Not sure how to compare with the singletons json_true/json_false
    # when the object might be an instance of the Adapter from
    # pycket_json_adapter... so I think this is the best we can do
    return make_boolean(tmp_b.tostring() == "true")
  assert False, "internal: couldn't make a term from json"

if we_are_translated():
  from pycket import pycket_json
  def string_to_term(s):
    json = pycket_json.loads(s)
    return json_to_term(json)
else:
  import json
  import pycket_json_adapter as pja
  def string_to_term(s):
    adapted = pja.adapt(json.loads(s))
    return json_to_term(adapted)

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

  def mark_static(self):
    pass

class W_EmptyEnvironment(W_Environment):
  def lookup(self, y):
    print "Variable %s not bound" % y.to_string()
    assert False
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
  def __init__(self, xs, vs, env):
    W_Environment.__init__(self)
    self.xs = W_TermList(xs)
    self.vs = W_TermList(vs)
    self.env = env

  @jit.unroll_safe
  def lookup(self, y):
    for x, v in izip2(self.xs, self.vs):
      if x.atoms_equal(y):
        return v
    return self.env.lookup(y)

  @jit.unroll_safe
  def is_bound(self, y):
    for x in self.xs:
      if x.atoms_equal(y):
        return True
    return self.env.is_bound(y)

def is_environment(v):
  return isinstance(v, W_Environment)

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
  return W_MultipleEnvironment(xs, vs, env)

@jit.unroll_safe
def environment_empty(t):
  [] = [x for x in W_TermList(t)]
  return W_EmptyEnvironment()


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

if __name__ == "__test__":
  pytest.main([__file__, "-q"])

if __name__ == "__main__":
  import os
  if "JAM_TEST" in os.environ:
    import runpy
    runpy.run_path(__file__, None, "__test__")
