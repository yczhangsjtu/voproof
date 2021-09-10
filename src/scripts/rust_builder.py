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

  def assign(self, right=None):
    self.append("=")
    if right is not None:
      self.append(right)
    return self

  def eol(self):
    return self.append("\n")

  def dumpr(self):
    if len(self.stack) > 0:
      raise Exception("Stack is not empty")
    return "".join([rust(arg) for arg in self.items])


class ExpressionVectorRust(object):
  def __init__(self, expr, length):
    self.expr = expr
    self.length = sympify(length)

  def dumpr(self):
    return "(0..%s).map(|i| %s).collect::<Vec<F>>()" \
           % (rust(self.length), rust(self.expr))


class AccumulationVectorRust(object):
  def __init__(self, expr, length, accumulator="sum"):
    super(AccumulationVector, self).__init__()
    self.expr = expr
    self.length = sympify(length)
    self.accumulator = accumulator

  def dumpr(self):
    return "(0..%s).scan(F::zero(), |acc, i| {*acc = *acc + (%s); Some(*acc)})" \
           ".collect::<Vec<F>>()" % (rust(self.length), rust(self.expr))


class SumAccumulationVector(AccumulationVector):
  def __init__(self, named_vector, length):
    super(SumAccumulationVector, self).__init__(named_vector.slice("j"),
                                                length, "sum")


class ProductAccumulationDivideVector(AccumulationVector):
  def __init__(self, v1, v2, length):
    super(ProductAccumulationDivideVector, self).__init__(
        "\\left(%s/%s\\right)" % (v1.slice("j").dumps(), v2.slice("j").dumps()),
        length, "prod")


def add_paren_if_add(expr):
  if isinstance(expr, Add):
    return "\\left(%s\\right)" % latex(expr)
  return tex(expr)


def add_paren_if_not_atom(vector):
  if not vector.is_atom():
    return "\\left(%s\\right)" % tex(vector)
  return tex(vector)


