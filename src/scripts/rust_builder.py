from sympy import Symbol, latex, sympify, Integer, Expr,\
                  simplify, Max, Add, Mul, Pow, srepr
from rust import rust_code, rust_code_to_field, force_lowercase


sym_i = Symbol("i")
rust_zero = "E::Fr::zero()"
rust_one = "E::Fr::one()"

def keep_alpha_number(s):
  return "".join([c for c in s if c.isalnum()])


def rust(expr, to_field=False):
  if isinstance(expr, str):
    return expr
  if hasattr(expr, "dumpr"):
    return expr.dumpr()
  if isinstance(expr, Expr):
    return rust_code(expr) if not to_field else rust_code_to_field(expr)
  return str(expr)


def to_field(expr):
  if isinstance(expr, Integer) or isinstance(expr, int):
    if expr == 0:
      return "E::Fr::zero()"
    if expr == 1:
      return "E::Fr::one()"
    if expr > 0:
      return rust(RustBuilder().func("to_field::<E::Fr>").append_to_last(expr))
    return rust(RustBuilder().append("-").func("to_field::<E::Fr>").append_to_last(-expr))
  return rust(expr)


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
    self.expand_lines = False

  def append(self, item):
    if isinstance(item, list):
      self.items += item
    else:
      self.items.append(item)
    return self
  
  def __len__(self):
    return len(self.items)

  def __getitem__(self, index):
    return self.items[index]

  def dumpr(self):
    if self.expand_lines and len(self.items) > 0:
      return "\n          " + ",\n          ".join([rust(item) for item in self.items])
    else:
      return ", ".join([rust(item) for item in self.items])


class FunctionCall(RustList):
  def __init__(self, func_name):
    super(FunctionCall, self).__init__()
    self.func_name = func_name
    self.expand_lines = True

  def dumpr(self):
    return "%s(%s)" % (self.func_name, super(FunctionCall, self).dumpr())


class RustMacro(FunctionCall):
  def __init__(self, macro_name, *args):
    super(RustMacro, self).__init__("%s!" % macro_name)
    self.macro_name = macro_name
    if (isinstance(args, list) or isinstance(args, tuple)) and len(args) > 0:
      for arg in args:
        self.append(arg)


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
    return self

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

  def plus_assign(self, right=None):
    self.append("+=")
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


def rust_builder_macro(macro_name, *args):
  return RustBuilder().append(RustMacro(macro_name, *args))


class _ArgName(object):
  def __init__(self, argname):
    self.argname = argname


class _ArgProcess(object):
  def __init__(self, func, *argnames):
    self.argnames = argnames
    self.func = func


rust_macro_list = [
    ("commit_scalar", None, ("c"), ("vk", _ArgName("c"))),
    ("expression_vector_to_vector", "expression_vector_to_vector_i", ("v", "expr"),
      (_ArgName("v"), sym_i, _ArgName("expr"))),
    ("assert_eq", None, ("a", "b"), ()),
    ("eval_vector_as_poly", None, ("v", "z"), ()),
    ("eval_vector_expression", "eval_vector_expression_i", ("z", "expr", "n"),
      (_ArgName("z"), sym_i, _ArgName("expr"), _ArgName("n"))),
    ("vector_concat", None, None, ()),
    ("check_vector_eq", None, ("v", "expr", "info"),
      (_ArgName("v"), _ArgName("expr"), _ArgProcess(lambda info: '"%s"' % info, "info"))),
    ("define_vec_mut", None, ("v", "expr"), ()),
    ("define_vec", None, ("v", "expr"), ()),
    ("define_mut", None, ("v", "expr"), ()),
    ("define", None, ("v", "expr"), ()),
    ("poly_from_vec", None, ("v"), ()),
    ("vec", None, None, ()),
    ("vec", "vec_size", ("e", "length"),
      (_ArgProcess(lambda e, length:
        "%s; (%s) as usize" % (rust(e), rust(length)),
        "e", "length"), )),
    ("linear_combination", None, None, ()),
    ("linear_combination_base_zero", None, None, ()),
    ("sum", None, None, ()),
    ("expression_vector", "expression_vector_i", ("expr", "length"),
      (sym_i, _ArgName("expr"), _ArgName("length"))),
    ("add_vector_to_vector", None, ("u", "v"), ()),
    ("add_expression_vector_to_vector", "add_expression_vector_to_vector_i", ("v", "expr"),
      (_ArgName("v"), sym_i, _ArgName("expr"))),
    ("check_poly_eval", None, ("poly", "point", "value", "info"),
      (_ArgName("poly"), _ArgName("point"), _ArgName("value"),
       _ArgProcess(lambda info: '"%s"' % info, "info"))),
    ("fmt_ff_vector", None, ("v"), ()),
    ("define_generator", None, (), ("gamma", "E")),
    ("init_size", None, ("name", "attr"), (_ArgName("name"), _ArgName("attr"), "size")),
    ("sample_randomizers", None, (), ("rng", )),
    ("concat_matrix_vertically", None,
      ("result", "h", "arows", "brows", "crows",
        "acols", "bcols", "cols", "avals", "bvals", "cvals"), ()),
    ("int_array_to_power_vector", None, ("v", "gamma"), ()),
    ("define_int_array_to_power_vector", None, ("name", "v", "gamma"), ()),
    ("define_clone_vector", None, ("name", "v"), ()),
    ("define_hadamard_vector", None, ("name", "u", "v"), ()),
    ("define_matrix_vectors", None, ("u", "w", "v", "M", "gamma"), ()),
    ("commit_vector", None, ("cm", "v", "deg"),
      (_ArgName("cm"), _ArgName("v"), "powers_of_g", _ArgName("deg"))),
    ("commit_vector", "commit_vector_with_pk", ("cm", "v", "deg"),
      (_ArgName("cm"), _ArgName("v"), "pk.powers", _ArgName("deg"))),
    ("define_sparse_mvp_vector", None, ("name", "M", "v", "H", "K"), ()),
    ("define_left_sparse_mvp_vector", None, ("name", "M", "v", "H", "K"), ()),
    ("define_concat_vector", None, None, ()),
    ("sparse_mvp_vector", None, ("M", "v", "H", "K"), ()),
    ("define_zero_pad_concat_vector", None, None, ()),
    ("redefine_zero_pad_concat_vector", None, None, ()),
    ("define_poly_from_vec", None, ("poly", "v"), ()),
    ("get_randomness_from_hash", None, None, ()),
    ("define_expression_vector", "define_expression_vector_i", ("name", "expr", "n"),
      (_ArgName("name"), sym_i, _ArgName("expr"), _ArgName("n"))),
    ("define_expression_vector_inverse", "define_expression_vector_inverse_i",
      ("name", "expr", "n"), (_ArgName("name"), sym_i, _ArgName("expr"), _ArgName("n"))),
    ("minus", None, ("u", "v"), ()),
    ("minus_i64", None, ("u", "v"), ()),
    ("neg", None, ("u"), ()),
    ("define_concat_neg_vector", None, ("name", "u", "v"), ()),
    ("define_concat_uwinverse_vector", None, ("name", "v", "mu", "u", "nu", "w"), ()),
    ("accumulate_vector_plus", None, ("v"), ()),
]


def _rust_macro(name, argnames, outargs, *args):
  if argnames is None:
    return RustMacro(name, *args)

  if len(args) != len(argnames):
    raise Exception("Macro %s Expect %d arguments (%s), got %d" %
        (name, len(argnames), ",".join(argnames), len(args)))

  if len(outargs) == 0:
    return RustMacro(name, *args)

  argdict = {name: value for name, value in zip(argnames, args)}

  macro = RustMacro(name)
  for e in outargs:
    if isinstance(e, _ArgName):
      macro.append(argdict[e.argname])
    elif isinstance(e, _ArgProcess):
      macro.append(e.func(*(argdict[argname] for argname in e.argnames)))
    else:
      macro.append(e)
  return macro


def _rust_builder_macro(name, argnames, outargs, *args):
  return RustBuilder(_rust_macro(name, argnames, outargs, *args))


current_module = __import__(__name__)
for macro_name, funcname, argnames, outargs in rust_macro_list:
  if funcname == None:
    funcname = macro_name
  setattr(
      current_module,
      "rust_%s" % funcname,
      (lambda macro_name, argnames, outargs:
        lambda *args:
          _rust_macro(macro_name, argnames, outargs, *args))(
        macro_name, argnames, outargs
      ))
  setattr(
      current_module,
      "rust_builder_%s" % funcname,
      (lambda macro_name, argnames, outargs:
        lambda *args:
          _rust_builder_macro(macro_name, argnames, outargs, *args))(
        macro_name, argnames, outargs
      ))

