from sympy import Symbol, latex, sympify, Integer, Expr,\
                  simplify, Max, Add, Mul, Pow, srepr


def keep_alpha_number(s):
  return "".join([c for c in s if c.isalnum()])


def rust(expr):
  if isinstance(expr, str):
    return expr
  if hasattr(expr, "dumpr"):
    return expr.dumpr()
  return str(expr)


def to_field(expr):
  if isinstance(expr, Integer):
    if expr == 0:
      return "F::zero()"
    if expr > 0:
      return rust(RustBuilder().func("to_field::<F>").append_to_last(expr))
    return rust(RustBuilder().append("-").func("to_field::<F>").append_to_last(-expr))
  return rust(expr)

class Samples(object):
  def __init__(self):
    self.items = []

  def append(self, item):
    self.items.append(item)

  def dumpr(self):
    ret = RustBuilder()
    for item in self.items:
      ret.let(item).assign_func("sample_field::<F, _>") \
         .append_to_last("rng").end()
    return rust(ret)


class RustArg(object):
  def __init__(self, name, is_ref=False, is_mutable=False):
    self.name = name
    self.is_ref = is_ref
    self.is_mutable = is_mutable

  def dumpr(self):
    if not self.is_ref:
      return dumpr(self.name)
    if self.is_mutable:
      return "&mut %s" % dumpr(self.name)
    return "&%s" % dumpr(self.name)


def ref(name):
  return RustArg(name, is_ref=True)


def mut(name):
  return RustArg(name, is_ref=True, is_mutable=True)


class RustList(object):
  def __init__(self):
    self.items = []

  def append(self, item):
    if isinstance(item, list):
      self.items += item
    else:
      self.items.append(item)
    return self

  def dumpr(self):
    return ", ".join([rust(item) for item in self.items])


class FunctionCall(RustList):
  def __init__(self, func_name):
    super(FunctionCall, self).__init__()
    self.func_name = func_name

  def dumpr(self):
    return "%s(%s)" % (self.func_name, super(FunctionCall, self).dumpr())


class RustMacro(FunctionCall):
  def __init__(self, macro_name):
    super(RustMacro, self).__init__("%s!" % macro_name)


class Tuple(RustList):
  def __init__(self):
    super(Tuple, self).__init__()

  def dumpr(self):
    return "(%s)" % super(Tuple, self).dumpr()


class RustBuilder(object):
  def __init__(self, *args):
    self.items = list(args)
    self.stack = []

  def append(self, right):
    if isinstance(right, list):
      self.items += right
    elif isinstance(right, RustBuilder):
      self.items += right.items
    else:
      self.items.append(right)
    return self

  def append_to_last(self, right):
    if hasattr(self.items[-1], 'append'):
      self.items[-1].append(right)
    return self
    raise Exception("Cannot append to last element of type %s"
                    % type(self.items[-1]))

  def let(self, right=None):
    self.append("let")
    if right is not None:
      self.space(right)
    return self

  def letmut(self, right=None):
    self.append("let mut")
    if right is not None:
      self.space(right)
    return self

  def func(self, right):
    if isinstance(right, str):
      return self.append(FunctionCall(right))
    elif isinstance(right, FunctionCall):
      return self.append(right)
    raise Exception("Cannot call type %s" % type(right))

  def invoke_method(self, right):
    self.append(".")
    if isinstance(right, str):
      return self.append(FunctionCall(right))
    elif isinstance(right, FunctionCall):
      return self.append(right)
    raise Exception("Cannot call type %s" % type(right))

  def attribute(self, right):
    self.append(".")
    if right is not None:
      self.append(right)

  def assign_func(self, right):
    return self.assign().func(right)

  def space(self, right=None):
    self.append(" ")
    if right is not None:
      self.append(right)
    return self

  def space_around(self):
    self.append(" ")
    self.append(right)
    self.append(" ")
    return self

  def comma(self, right=None):
    self.append(",")
    if right is not None:
      self.append(right)
    return self

  def plus(self, right=None):
    self.append("+")
    if right is not None:
      self.append(right)
    return self

  def minus(self, right=None, align=False):
    self.append("-")
    if right is not None:
      self.append(right)
    return self

  def mul(self, right=None):
    self.append("*")
    if right is not None:
      self.append(right)
    return self

  def slash(self, right=None):
    self.append("/")
    if right is not None:
      self.append(right)
    return self

  def paren(self, right=None):
    self.append("\\left(")
    if right is not None:
      self.append(right)
    self.append("\\right)")
    return self

  def start_env(self, name, marker):
    self.append(marker)
    self.stack.append(name)
    return self

  def end_env(self, name, marker):
    if not self.stack[-1] == name:
      raise Exception("Cannot end %s. Last time is %s" % (name, self.stack[-1]))
    self.stack.pop()
    self.append(marker)
    return self

  def start_paren(self):
    return self.start_env("paren", "(")

  def end_paren(self):
    return self.end_env("paren", ")")

  def assign(self, right=None):
    self.append("=")
    if right is not None:
      self.append(right)
    return self

  def eol(self):
    return self.append("\n" + " " * 12)
  
  def end(self):
    return self.append(";\n" + " " * 8)

  def dumpr(self):
    if len(self.stack) > 0:
      raise Exception("Stack is not empty")
    return "".join([rust(arg) for arg in self.items])


class ExpressionVectorRust(object):
  def __init__(self, expr, length):
    self.expr = expr
    self.length = sympify(length)

  def dumpr(self):
    return "(1..=%s).map(|i| %s).collect::<Vec<F>>()" \
           % (rust(self.length), rust(self.expr))


class AccumulationVectorRust(object):
  def __init__(self, expr, length, accumulator="*"):
    super(AccumulationVectorRust, self).__init__()
    self.expr = expr
    self.length = sympify(length)
    self.accumulator = accumulator

  def dumpr(self):
    return "(1..=%s).scan(F::zero(), |acc, &mut i| {*acc = *acc %s (%s); Some(*acc)})" \
           ".collect::<Vec<F>>()" % (rust(self.length), self.accumulator, rust(self.expr))


class SumAccumulationVectorRust(AccumulationVectorRust):
  def __init__(self, named_vector, length):
    super(SumAccumulationVectorRust, self).__init__(named_vector.slice("i-1"), length, "+")


class ProductAccumulationDivideVectorRust(AccumulationVectorRust):
  def __init__(self, v1, v2, length):
    super(ProductAccumulationDivideVectorRust, self).__init__(
        "(%s/%s)" % (v1.slice("i-1").dumpr(), v2.slice("i-1").dumpr()), length, "*")


def add_paren_if_add(expr):
  if isinstance(expr, Add):
    return "(%s)" % rust(expr)
  return rust(expr)


def add_paren_if_not_atom(vector):
  if not vector.is_atom():
    return "(%s)" % rust(vector)
  return rust(vector)


