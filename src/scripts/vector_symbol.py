from sympy import Symbol, latex, sympify, Integer, Expr,\
                  simplify, Max, Add, Mul, Pow, srepr
from sympy.abc import alpha, X
from sympy.core.numbers import Infinity
from latex_builder import tex
from rust_builder import *


class _NamedBasic(object):
  def __init__(self, name, modifier=None, subscript=None, has_prime=False,
               _type=None):
    if "_" in name and subscript is None:
      name, subscript = name.split("_")
    self.name = name
    self.modifier = modifier
    self.subscript = subscript
    self.has_prime = has_prime
    self._type = _type
    self._cached_expr = None

  def key(self):
    ret = ["named_basic", self.name]
    ret.append(self.modifier if self.modifier is not None else "")
    ret.append(tex(self.subscript) if self.subscript is not None else "")
    ret.append("prime" if self.has_prime else "")
    ret.append(self._type if self._type is not None else "")
    return ":".join(ret)

  def sub(self, subscript):
    self.subscript = sympify(subscript)
    self._cached_expr = None
    return self

  def tilde(self):
    self.modifier = "tilde"
    self._cached_expr = None
    return self

  def hat(self):
    self.modifier = "hat"
    self._cached_expr = None
    return self

  def bar(self):
    self.modifier = "bar"
    self._cached_expr = None
    return self

  def prime(self):
    self.has_prime = True
    self._cached_expr = None
    return self

  def dumps(self):
    if self._cached_expr is not None:
      return self._cached_expr

    # The latex(Symbol(...)) here is to automatically add
    # slash to greek letter or ell, etc.
    ret = latex(Symbol(self.name))
    if self._type is not None:
      ret = "\\%s{%s}" % (self._type, ret)
    if self.modifier is not None:
      ret = "\\%s{%s}" % (self.modifier, ret)
    if self.subscript is not None:
      ret = "{%s}_{%s}" % (ret, latex(self.subscript))
    if self.has_prime:
      ret = "%s'" % ret

    self._cached_expr = ret
    return self._cached_expr

  # Dump rust name
  def dumpr(self):
    ret = [force_lowercase(self.name)]
    if self._type is not None:
      ret.append(self._type)
    if self.modifier is not None:
      ret.append(self.modifier)
    if self.subscript is not None:
      ret.append(keep_alpha_number(str(self.subscript)))
    if self.has_prime:
      ret.append("prime")
    return "_".join(ret)

__name_counters = {}


def get_name(name, modifier=None, has_prime=False, _type=None):
  global __name_counters
  key = _NamedBasic(name, modifier=modifier,
                    has_prime=has_prime, _type=_type).key()
  if key not in __name_counters:
    __name_counters[key] = 0
    return name
  else:
    __name_counters[key] += 1
    return "%s_%d" % (name, __name_counters[key])


def reset_name_counters():
  global __name_counters
  __name_counters = {}


class NamedVector(_NamedBasic):
  def __init__(self, name, modifier=None, subscript=None, has_prime=False):
    super(NamedVector, self).__init__(name, modifier=modifier, subscript=subscript,
                                      has_prime=has_prime, _type="vec")
    self.local_evaluate = False
    self.hint_computation = None
    self.randomizers = None
    self._is_preprocessed = False

  def slice(self, start, end=None):
    return VectorSlice(self, start, end)

  def is_atom(self):
    return True

  def shifts(self):
    return []

  def to_named_vector_poly(self):
    ret = NamedVectorPolynomial(self)
    ret._is_preprocessed = self._is_preprocessed
    return ret

  def get_poly_with_same_name(self):
    return get_named_polynomial(self.name,
                                modifier=self.modifier,
                                has_prime=self.has_prime)

  def __add__(self, other):
    return VectorCombination._from(self).__add__(other)

  def __radd__(self, other):
    return self.__add__(other)

  def __neg__(self):
    return VectorCombination._from(self).__neg__()

  def __sub__(self, other):
    return VectorCombination._from(self).__sub__(other)

  def __rsub__(self, other):
    return VectorCombination._from(self).__rsub__(other)

  def __mul__(self, other):
    return VectorCombination._from(self).__mul__(other)

  def __rmul__(self, other):
    return self.__mul__(other)

  def __div__(self, other):
    return VectorCombination._from(self).__div__(other)

  def shift(self, length):
    return self.__mul__(UnitVector(length + 1))

  def dumpr_at_index(self, index):
    return rust(RustMacro("vector_index").append([rust_pk(self), rust(index)]))


def get_named_vector(name, modifier=None, has_prime=False):
  name = get_name(name, modifier=modifier, has_prime=has_prime, _type="vec")
  return NamedVector(name, modifier=modifier, has_prime=has_prime)


def get_named_vectors(names, modifier=None, has_prime=False):
  return [get_named_vector(name, modifier=modifier, has_prime=has_prime) for name in names]


class VectorSlice(object):
  def __init__(self, named_vector, start, end=None):
    super(VectorSlice, self).__init__()
    self.named_vector = named_vector
    self.start = sympify(start)
    self.end = None if end is None else sympify(end)

  def get_range(self, start, end):
    if self.end is None:
      return "[%s]" % start
    if self.end == Infinity:
      return "[%s..]" % start
    slc = "[%s..%s]" % (start, end)
    return slc

  def dumps(self):
    end = latex(self.end) if self.end is not None else ""
    return "{%s}_{%s}" % (self.named_vector.dumps(),
                          self.get_range(latex(self.start), end))

  def dumpr(self):
    end = str(self.end) if self.end is not None else ""
    return "%s%s" % (self.named_vector.dumpr(),
                     self.get_range(str(self.start), end))


class UnitVector(object):
  def __init__(self, position):
    # position can be Symbol, Expr or Integer
    self.position = simplify(sympify(position))

  def dumps(self):
    return "\\vec{e}_{%s}" % (latex(self.position))
  
  def key(self):
    return "unit_vector:%s" % (latex(self.position))

  def is_atom(self):
    return True

  def shifts(self):
    return []
  
  def to_poly_expr(self, var):
    return var ** (self.position - 1)

  def __add__(self, other):
    return SparseVector._from(self).__add__(other)

  def __radd__(self, other):
    return self.__add__(other)

  def __neg__(self):
    return SparseVector._from(self).__neg__()

  def __sub__(self, other):
    return SparseVector._from(self).__sub__(other)

  def __rsub__(self, other):
    return SparseVector._from(self).__rsub__(other)

  def __mul__(self, other):
    if isinstance(other, UnitVector):
      return UnitVector(self.position + other.position - 1)
    return SparseVector._from(self).__mul__(other)

  def __rmul__(self, other):
    return self.__mul__(other)

  def __div__(self, other):
    return SparseVector._from(self).__div__(other)
  
  def dumpr_at_index(self, index):
    return rust(RustMacro("delta").append([rust(index), rust(self.position)]))
  
  def reverse_omega(self, omega):
    return SparseVector._from(self).reverse_omega(omega)


class CoeffMap(object):
  def __init__(self):
    self._dict = {}

  def is_empty(self):
    return len(self._dict) == 0

  def set(self, keyed, value):
    if value is None:
      raise Exception("Value should not be None")
    key = keyed if isinstance(keyed, str) else keyed.key()
    if value == 0 or (isinstance(value, CoeffMap) and value.is_empty()) or \
       (isinstance(value, Expr) and simplify(value) == 0):
      self.remove_if_has(key)
    else:
      self._dict[key] = (keyed, value)

    return self

  def get(self, keyed):
    return self._dict[keyed.key()][1]

  def has(self, keyed):
    return keyed.key() in self._dict

  def remove_if_has(self, keyed):
    key = keyed if isinstance(keyed, str) else keyed.key()
    if key in self._dict:
      del self._dict[key]

  def items(self):
    return self._dict.items()

  def copy(self):
    ret = CoeffMap()
    for key, value in self._dict.items():
      if hasattr(value, 'copy'):
        ret._dict[key] = value.copy()
      else:
        ret._dict[key] = value
    return ret

  def __add__(self, other):
    ret = self.copy()
    for key, keyed_value in other._dict.items():
      keyed, value = keyed_value
      if key in ret._dict:
        res = ret._dict[key][1] + value
        if res != 0:
          ret._dict[key] = (keyed, res)
        else:
          del ret._dict[key]
      else:
        ret._dict[key] = (keyed, value)

    return ret

  def __neg__(self):
    ret = CoeffMap()
    for key, keyed_value in self._dict.items():
      keyed, value = keyed_value
      ret._dict[key] = (keyed, -value)
    return ret

  def __radd__(self, other):
    return self.__add__(other)
  
  def __sub__(self, other):
    return self.__add__(-other)
  
  def __rsub__(self, other):
    return self.__neg__()._add__(other)
  
  def __mul__(self, other):
    ret = CoeffMap()
    for key, keyed_value in self._dict.items():
      keyed, value = keyed_value
      if value is None:
        for _key, _keyed_value in self._dict.items():
          _keyed, _value = _keyed_value
          if hasattr(_keyed, "dumps"):
            _keyed = _keyed.dumps()
          if hasattr(_value, "dumps"):
            _value = _value.dumps()
          print(_key, _keyed, _value)
        raise Exception("Value should not be None: key = %s, keyed = %s"
                        % (key, tex(keyed)))
      ret._dict[key] = (keyed, value * other)
    return ret

  def __rmul__(self, other):
    return self.__mul__(other)
  
  def __div__(self, other):
    ret = CoeffMap()
    for key, keyed_value in self._dict.items():
      keyed, value = keyed_value
      ret._dict[key] = (keyed, value / other)
    return ret


class SparseVector(CoeffMap):
  def __init__(self):
    super(SparseVector, self).__init__()

  def set(self, position, value):
    value = simplify(sympify(value))
    if not isinstance(position, UnitVector):
      unit_vector = UnitVector(position)
    else:
      unit_vector = position
    if value == 0:
      self.remove_if_has(unit_vector)
      return self
    return super(SparseVector, self).set(unit_vector, value)

  def get(self, position):
    if not isinstance(position, UnitVector):
      unit_vector = UnitVector(position)
    else:
      unit_vector = position
    if not self.has(unit_vector):
      return sympify(0)
    return super(SparseVector, self).get(unit_vector)
  
  def copy(self):
    return SparseVector._from(self)

  def _from(other):
    v = SparseVector()
    if isinstance(other, int):
      return v.set(1, sympify(other))
    if isinstance(other, str):
      return v.set(1, sympify(other))
    if isinstance(other, Expr):
      return v.set(1, other)
    if isinstance(other, UnitVector):
      return v.set(other, sympify(1))
    if isinstance(other, SparseVector) or type(other) == CoeffMap:
      for key, value in other.items():
        v._dict[key] = value
      return v
    raise Exception("Cannot convert %s to SparseVector" % (type(other)))

  def __add__(self, other):
    if isinstance(other, VectorCombination) or \
       isinstance(other, StructuredVector) or \
       isinstance(other, PowerVector):
      return other.__add__(self)

    if not isinstance(other, SparseVector):
      other = SparseVector._from(other)

    ret = super(SparseVector, self).__add__(other)
    return SparseVector._from(ret)

  def __radd__(self, other):
    return self.__add__(other)

  def __neg__(self):
    return SparseVector._from(super(SparseVector, self).__neg__())

  def __sub__(self, other):
    return self.__add__(-other)

  def __rsub__(self, other):
    return self.__neg__().__add__(other)

  def __mul__(self, other):
    if isinstance(other, UnitVector):
      other = SparseVector._from(other)

    if isinstance(other, PowerVector):
      other = StructuredVector._from(other)

    if isinstance(other, SparseVector):
      v = SparseVector()
      for left_key, vector_coeff in self.items():
        left_vector, left_coeff = vector_coeff
        for right_key, vector_coeff_2 in other.items():
          right_vector, right_coeff = vector_coeff_2
          vector = left_vector * right_vector
          coeff = left_coeff * right_coeff
          if v.has(vector):
            v.set(vector, v.get(vector.position) + coeff)
          else:
            v.set(vector, coeff)
      return v

    if isinstance(other, StructuredVector) or isinstance(other, VectorCombination):
      return other.__mul__(self)
    return SparseVector._from(super(SparseVector, self).__mul__(other))

  def __rmul__(self, other):
    return self.__mul__(other)

  def __div__(self, other):
    return SparseVector._from(super(SparseVector, self).__div__(other))

  def dumps(self):
    items = []
    for key, uv_coeff in self.items():
      unit_vector, coeff = uv_coeff
      items.append(_multiply_if_not_one(unit_vector.dumps(), coeff))

    if len(items) == 0:
      return "\\vec{0}"

    items_with_pluses = []
    for item in items:
      if not item.startswith("-") and len(items_with_pluses) > 0:
        items_with_pluses.append("+%s" % item)
      else:
        items_with_pluses.append(item)

    return "".join(items_with_pluses)

  def is_atom(self):
    return len(self._dict) == 1

  def shifts(self):
    return []

  def shift(self, length):
    return self.__mul__(UnitVector(length + 1))

  def to_poly_expr(self, var):
    items = []
    for key, uv_coeff in self.items():
      unit_vector, coeff = uv_coeff
      items.append(unit_vector.to_poly_expr(var) * coeff)
    return sum(items)

  def dumpr_at_index(self, index):
    ret = RustMacro("multi_delta").append(rust(index))
    for key, uv_coeff in self.items():
      unit_vector, coeff = uv_coeff
      ret.append([to_field(coeff), unit_vector.position])
    return rust(ret)

  def reverse_omega(self, omega):
    # f_v(X) => f_v(omega X^{-1})
    v = SparseVector()
    for key, uv_coeff in self.items():
      unit_vector, coeff = uv_coeff
      v.set(2 - unit_vector.position, coeff * (omega ** (unit_vector.position - 1)))
    return v


def _shift_if_not_zero(vec, shifted):
  if simplify(shifted) == 0:
    return vec
  return "{%s}^{\\to %s}" % (vec, tex(shifted))


def _multiply_if_not_one(vec, coeff):
  if simplify(coeff-1) == 0:
    return vec
  elif simplify(coeff+1) == 0:
    return "-%s" % vec
  else:
    if isinstance(coeff, Add):
      return "\\left(%s\\right)\\cdot %s" % (tex(coeff), vec)
    return "%s\\cdot %s" % (tex(coeff), vec)


def _dump_coeff_map_with_sparse_coeff(v):
  not_ones = []
  one = None
  for key, vec_value in v.items():
    vec, value = vec_value
    if key == "one":
      one = value.dumps()
      if len(one) == 0:
        raise Exception("value should not be empty: %s" % str(value))
    else:
      for key2, uv_coeff in value.items():
        unit_vector, coeff = uv_coeff
        shifted_vec = _shift_if_not_zero(vec.dumps(), unit_vector.position - 1)
        not_ones.append(_multiply_if_not_one(shifted_vec, coeff))

  if one is not None:
    not_ones.append(one)

  items = []
  for v in not_ones:
    if len(v) == 0:
      print(not_ones)
      raise Exception("v should not be empty")
    if not v.startswith("-") and len(items) > 0:
      items.append("+%s" % v)
    else:
      items.append(v)

  return "".join(items)


def _dumpr_at_index_for_sparse_coefficient(v, index):
  has_one = "one" in v._dict
  ret = rust_linear_combination(v._dict["one"][1].dumpr_at_index(index)) \
      if has_one else rust_linear_combination_base_zero()

  for key, vec_value in v.items():
    if key == "one":
      continue
    vec, value = vec_value
    for key2, uv_coeff in value.items():
      unit_vector, coeff = uv_coeff
      ret.append([
        to_field(coeff),
        vec.dumpr_at_index(rust_minus_i64(index, unit_vector.position))
      ])

  if len(ret) == 2 and not has_one:
    if ret[0] == to_field(1):
      return rust(ret[1])
    if ret[0] == to_field(-1):
      return rust(rust_neg(ret[1]))
    if ret[1] == to_field(1):
      return rust(ret[0])
    if ret[1] == to_field(-1):
      return rust(rust_neg(ret[0]))
    return rust(rust_mul(ret[0], ret[1]))

  return rust(ret)

class VectorCombination(CoeffMap):
  def __init__(self):
    super(VectorCombination, self).__init__()

  def copy(self):
    return VectorCombination._from(self)

  def _from(other):
    v = VectorCombination()
    if isinstance(other, int) or isinstance(other, str) or \
       isinstance(other, Expr) or isinstance(other, UnitVector):
      return v.set("one", StructuredVector._from(other))
    if isinstance(other, SparseVector) or isinstance(other, PowerVector):
      return v.set("one", StructuredVector._from(other))
    if isinstance(other, StructuredVector):
      return v.set("one", other.copy())
    if isinstance(other, NamedVector):
      return v.set(other, SparseVector._from(1))
    if isinstance(other, VectorCombination) or type(other) == CoeffMap:
      for key, value in other.items():
        v._dict[key] = value
      return v
    raise Exception("Cannot convert %s to VectorCombination" % (type(other)))

  def __add__(self, other):
    if not isinstance(other, VectorCombination):
      other = VectorCombination._from(other)

    ret = super(VectorCombination, self).__add__(other)
    return VectorCombination._from(ret)

  def __radd__(self, other):
    return self.__add__(other)

  def __neg__(self):
    return VectorCombination._from(super(VectorCombination, self).__neg__())

  def __sub__(self, other):
    return self.__add__(-other)

  def __rsub__(self, other):
    return self.__neg__().__add__(other)

  def __mul__(self, other):
    if isinstance(other, VectorCombination):
      raise Exception("VectorCombinations should not be multiplied together")
    if isinstance(other, StructuredVector):
      raise Exception("VectorCombination should not be multiplied with StructuredVector")
    return VectorCombination._from(super(VectorCombination, self).__mul__(other))

  def __rmul__(self, other):
    return self.__mul__(other)

  def __div__(self, other):
    return VectorCombination._from(super(VectorCombination, self).__div__(other))

  def is_atom(self):
    if len(self._dict) > 1:
      return False

    if len(self._dict) == 0:
      return True

    for key, vec_value in self.items():
      vec, value = vec_value
      return value.is_atom()

  def shift(self, length):
    return self.__mul__(UnitVector(length + 1))

  def shifts(self):
    lengths = []
    for key, vec_value in self.items():
      if key == "one":
        continue
      vec, value = vec_value
      for key2, uv_coeff in value.items():
        unit_vector, coeff = uv_coeff
        lengths.append(unit_vector.position - 1)
    return lengths

  def dumps(self):
    return _dump_coeff_map_with_sparse_coeff(self)

  def dumpr_at_index(self, index):
    return _dumpr_at_index_for_sparse_coefficient(self, index)

class PowerVector(object):
  def __init__(self, alpha, size):
    # alpha and size can be Symbol or Integer
    self.alpha = simplify(sympify(alpha))
    self.size = simplify(sympify(size))

  def key(self):
    return "power_vector:%s:%s" % (latex(self.alpha), latex(self.size))

  def dumps(self):
    return "\\vec{%s}^{%s}" % (latex(self.alpha), latex(self.size))

  def is_atom(self):
    return True

  def shifts(self):
    return []

  def __add__(self, other):
    return StructuredVector._from(self).__add__(other)

  def __radd__(self, other):
    return self.__add__(other)

  def __neg__(self):
    return StructuredVector._from(self).__neg__()

  def __sub__(self, other):
    return StructuredVector._from(self).__sub__(other)

  def __rsub__(self, other):
    return StructuredVector._from(self).__rsub__(other)

  def __mul__(self, other):
    if isinstance(other, StructuredVector):
      raise Exception("StructuredVector cannot be multiplied with power vector")
    if isinstance(other, PowerVector):
      raise Exception("PowerVectors cannot be multiplied together")
    return StructuredVector._from(self).__mul__(other)

  def __rmul__(self, other):
    return self.__mul__(other)

  def __div__(self, other):
    return StructuredVector._from(self).__div__(other)

  def shift(self, length):
    return self.__mul__(UnitVector(length + 1))

  def to_poly_expr(self, var):
    return ((self.alpha * var) ** self.size - Symbol("E::Fr::one()")) / (self.alpha * var - Symbol("E::Fr::one()"))
  
  def dumpr_at_index(self, index):
    if self.alpha != 1:
      return rust(RustMacro("power_vector_index").append([
          rust(self.alpha, to_field=True), self.size, index]))
    else:
      return rust(RustMacro("range_index").append([1, self.size, index]))

  def reverse_omega(self, omega):
    return StructuredVector._from(self).reverse_omega(omega)

class StructuredVector(CoeffMap):
  def __init__(self):
    super(StructuredVector, self).__init__()

  def copy(self):
    return StructuredVector._from(self)

  def _from(other):
    v = StructuredVector()
    if isinstance(other, int) or isinstance(other, str) or \
       isinstance(other, Expr) or isinstance(other, UnitVector):
      return v.set("one", SparseVector._from(other))
    if isinstance(other, SparseVector):
      return v.set("one", other.copy())
    if isinstance(other, PowerVector):
      return v.set(other, SparseVector._from(1))
    if isinstance(other, StructuredVector) or type(other) == CoeffMap:
      for key, value in other.items():
        v._dict[key] = value
      return v
    raise Exception("Cannot convert %s to StructuredVector" % (type(other)))

  def __add__(self, other):
    if isinstance(other, VectorCombination) or \
       isinstance(other, NamedVector):
      return other.__add__(self)

    if not isinstance(other, StructuredVector):
      other = StructuredVector._from(other)

    ret = super(StructuredVector, self).__add__(other)
    return StructuredVector._from(ret)

  def __radd__(self, other):
    return self.__add__(other)

  def __neg__(self):
    return StructuredVector._from(super(StructuredVector, self).__neg__())

  def __sub__(self, other):
    return self.__add__(-other)

  def __rsub__(self, other):
    return self.__neg__().__add__(other)

  def __mul__(self, other):
    if isinstance(other, StructuredVector):
      raise Exception("Structured vectors cannot be multiplied together")
    if isinstance(other, PowerVector):
      raise Exception("Structured vector cannot be multiplied with a PowerVector")
    return StructuredVector._from(super(StructuredVector, self).__mul__(other))

  def __rmul__(self, other):
    return self.__mul__(other)

  def __div__(self, other):
    return StructuredVector._from(super(StructuredVector, self).__div__(other))

  def dumps(self):
    return _dump_coeff_map_with_sparse_coeff(self)
  
  def is_atom(self):
    if len(self._dict) > 1:
      return False

    if len(self._dict) == 0:
      return True

    for key, vec_value in self.items():
      vec, value = vec_value
      return value.is_atom()

  def shifts(self):
    return []

  def shift(self, length):
    return self.__mul__(UnitVector(length + 1))

  def to_poly_expr(self, var):
    items = []
    for key, power_value in self.items():
      vector, value = power_value
      if key == "one":
        items.append(value.to_poly_expr(var))
      else:
        items.append(vector.to_poly_expr(var) * value.to_poly_expr(var))
    return sum(items)

  def dumpr_at_index(self, index):
    return _dumpr_at_index_for_sparse_coefficient(self, index)

  def reverse_omega(self, omega):
    ret = StructuredVector()
    for key, power_value in self.items():
      vector, value = power_value
      if key == "one":
        ret._dict[key] = value.reverse_omega(omega)
      else:
        # f(X) => f(omega X^{-1}) transforms the power vector to the coefficients of
        # (X^{-(k-1)}(alpha omega)^{k-1}) * (1 + (alpha omega)^{-1} X + ...)
        # which is a transformed power vector. The transformation is then applied
        # to the coefficient for this power vector
        ret._dict[key] = (PowerVector(1/(vector.alpha * omega), vector.size),
                          (value.reverse_omega(omega) *
                          ((vector.alpha * omega) ** (vector.size - 1)))
                            .shift(-vector.size + 1))
    return ret


class Matrix(_NamedBasic):
  def __init__(self, name, modifier=None, subscript=None, has_prime=False):
    super(Matrix, self).__init__(name, modifier, subscript, has_prime, _type = "mat")


class NamedPolynomial(_NamedBasic):
  def __init__(self, name, modifier=None, subscript=None, has_prime=False):
    super(NamedPolynomial, self).__init__(name, modifier, subscript, has_prime)
    self._local_evaluate = False
    self._is_preprocessed = False
    self._vector = None

  def local_evaluate(self):
    return self._local_evaluate

  def dumps(self):
    return "%s(X)" % super(NamedPolynomial, self).dumps()

  def dumps_var(self, var):
    return "%s(%s)" % (super(NamedPolynomial, self).dumps(), tex(var))

  def to_comm(self):
    return PolynomialCommitment(self)

  def to_vec(self):
    return NamedVector(self.name, self.modifier, self.subscript, self.has_prime)

  def dumpr(self):
    return "%s_poly" % super(NamedPolynomial, self).dumpr()

  def dumpr_at_index(self, index):
    return self._vector.dumpr_at_index(index)


class PolynomialCommitment(object):
  def __init__(self, polynomial):
    # Must be named polynomial or named vector polynomial
    self.polynomial = polynomial
    self._is_preprocessed = polynomial._is_preprocessed

  def dumps(self):
    if isinstance(self.polynomial, NamedPolynomial):
      return "\\mathsf{cm}_{%s}" % super(NamedPolynomial, self.polynomial).dumps()
    else: # NamedVectorPolynomial
      return "\\mathsf{cm}_{%s}" % self.polynomial.vector.dumps()
  
  def dumpr(self):
    if isinstance(self.polynomial, NamedPolynomial):
      return "cm_%s" % super(NamedPolynomial, self.polynomial).dumpr()
    else:
      return "cm_%s" % self.polynomial.vector.dumpr()


def get_named_polynomial(name, modifier=None, has_prime=False):
  name = get_name(name, modifier=modifier, has_prime=has_prime, _type="poly")
  return NamedPolynomial(name, modifier=modifier, has_prime=has_prime)


def rust_vk(comm):
  if hasattr(comm, "_is_preprocessed") and comm._is_preprocessed:
    return "vk.%s" % rust(comm)
  return rust(comm)


def rust_pk(comm):
  if hasattr(comm, "_is_preprocessed") and comm._is_preprocessed:
    return "pk.%s" % rust(comm)
  return rust(comm)


def rust_pk_vk(comm):
  if hasattr(comm, "_is_preprocessed") and comm._is_preprocessed:
    return "pk.verifier_key.%s" % rust(comm)
  return rust(comm)


class NamedVectorPolynomial(object):
  def __init__(self, named_vector):
    super(NamedVectorPolynomial, self).__init__()
    self.vector = named_vector
    self._is_preprocessed = False

  def local_evaluate(self):
    return self.vector.local_evaluate

  def key(self):
    return "named_vector_poly:%s" % self.vector.key()

  def dumps(self):
    return "f_{%s}(X)" % self.vector.dumps()

  def dumps_var(self, var):
    return "f_{%s}(%s)" % (self.vector.dumps(), tex(var))

  def to_comm(self):
    return PolynomialCommitment(self)

  def dumpr(self):
    return "%s_poly" % self.vector.dumpr()

  def dumpr_at_index(self, index):
    return self.vector.dumpr_at_index(index)


class PolynomialCombination(CoeffMap):
  def __init__(self):
    super(PolynomialCombination, self).__init__()

  def copy(self):
    return PolynomialCombination._from(self)

  def _from(other):
    v = PolynomialCombination()
    if isinstance(other, int):
      return v.set("one", sympify(other))
    if isinstance(other, str):
      return v.set("one", sympify(other))
    if isinstance(other, Expr):
      return v.set("one", other)
    if isinstance(other, NamedPolynomial) or \
       isinstance(other, NamedVectorPolynomial):
      return v.set(other, 1)
    if isinstance(other, PolynomialCombination):
      for key, value in other.items():
        v._dict[key] = value
      return v
    raise Exception("Cannot convert %s to PolynomialCombination" % (type(other)))

  def __add__(self, other):
    if not isinstance(other, PolynomialCombination):
      other = PolynomialCombination._from(other)

    ret = super(PolynomialCombination, self).__add__(other)
    return PolynomialCombination._from(ret)

  def __radd__(self, other):
    return self.__add__(other)

  def __neg__(self):
    return PolynomialCombination._from(super(PolynomialCombination, self).__neg__())

  def __sub__(self, other):
    return self.__add__(-other)

  def __rsub__(self, other):
    return self.__neg__().__add__(other)

  def __mul__(self, other):
    return PolynomialCombination._from(super(PolynomialCombination, self).__mul__(other))

  def __rmul__(self, other):
    return self.__mul__(other)

  def __div__(self, other):
    return PolynomialCombination._from(super(PolynomialCombination, self).__div__(other))

  def dumps_var(self, var):
    not_ones = []
    one = None
    for key, poly_coeff in self.items():
      poly, coeff = poly_coeff
      if key == "one":
        one = coeff.dumps()
      else:
        not_ones.append(_multiply_if_not_one(poly.dumps_var(var), coeff))

    if one is not None:
      not_ones.append(one)

    items = []
    for item in not_ones:
      if not item.startswith("-") and len(items) > 0:
        items.append("+%s" % item)
      else:
        items.append(item)

    return "".join(items)

  def dumps(self):
    return self.dumps_var("X")

  def is_atom(self):
    if len(self._dict) > 1:
      return False

    if len(self._dict) == 0:
      return True

    for key, poly_coeff in self.items():
      if key == "one":
        poly, coeff = poly_coeff
        return not isinstance(coeff, Add)
      return True


def expand_max(expr):
  ret = []
  if isinstance(expr, Add):
    for arg in expr.args:
      subs = expand_max(arg)
      if len(ret) == 0:
        ret = subs
      else:
        ret = [a + b for a in ret for b in subs]
    return ret

  if isinstance(expr, Max):
    for arg in expr.args:
      ret += expand_max(arg)
    return ret

  if isinstance(expr, Symbol) or isinstance(expr, Integer):
    return [expr]

  if isinstance(expr, Mul):
    for arg in expr.args:
      subs = expand_max(arg)
      if len(ret) == 0:
        ret = subs
      else:
        ret = [a * b for a in ret for b in subs]
    return ret

  raise Exception("Unexpected type: %s" % type(expr))


def simplify_max(expr, larger=None, smaller=None):
  # print("Before: %s" % latex(expr))
  # print("Using: %s > %s" % (latex(larger), latex(smaller)))
  if larger is not None:
    diff = Symbol(get_name("diff"), positive=True)
    expr = expr.subs({larger: diff + smaller})

  items = expand_max(expr)
  # print("Items %s" % ",".join([latex(item) for item in items]))
  expr = Max(*items)

  if larger is not None:
    expr = expr.subs({diff: larger - smaller})
    items = expand_max(expr)
    expr = Max(*items)
    # print("Items %s" % ",".join([latex(item) for item in items]))

  # print("After: %s" % latex(expr))
  return expr


def simplify_max_with_hints(expr, hints):
  for larger, smaller in hints:
    expr = simplify_max(expr, larger, smaller)
  return expr


class NamedVectorPair(object):
  def __init__(self, u, v):
    if not isinstance(u, NamedVector) and not isinstance(v, NamedVector):
      raise Exception("At least one of u, v should be NamedVector")
    if not isinstance(u, NamedVector) and u is not None:
      raise Exception("u should be either NamedVector or None")
    if not isinstance(v, NamedVector) and v is not None:
      raise Exception("v should be either NamedVector or None")
    self.u = u
    self.v = v

  def key(self):
    left = self.u.key() if self.u is not None else "one"
    right = self.v.key() if self.v is not None else "one"
    return left + ":vector_pair:" + right


class StructuredVectorPair(object):
  def __init__(self, u, v):
    if not isinstance(u, StructuredVector) and not isinstance(v, StructuredVector):
      raise Exception("At least one of u, v should be StructuredVector")
    if not isinstance(u, StructuredVector) and u is not None:
      raise Exception("u should be either StructuredVector or None")
    if not isinstance(v, StructuredVector) and v is not None:
      raise Exception("v should be either StructuredVector or None")
    self.u = u
    self.v = v

  def key(self):
    left = self.u.key() if self.u is not None else "one"
    right = self.v.key() if self.v is not None else "one"
    return left + ":struct_vector_pair:" + right

  def _from(other):
    if isinstance(other, int) or isinstance(other, str) or \
       isinstance(other, Expr) or isinstance(other, UnitVector) or \
       isinstance(other, SparseVector) or isinstance(other, PowerVector):
      other = StructuredVector._from(other)
    if isinstance(other, StructuredVector):
      return StructuredVectorPair(None, other)

  def copy(self):
    left = self.u.copy() if self.u is not None else None
    right = self.v.copy() if self.v is not None else None
    return StructuredVectorPair(left, right)

  def __neg__(self):
    if self.u is not None:
      return StructuredVectorPair(-self.u, self.v)
    return StructuredVectorPair(self.u, -self.v)


class StructuredVectorPairCombination(object):
  def __init__(self):
    self.pairs = []
    self.one = None

  def copy(self):
    return StructuredVectorPairCombination._from(self)

  def add_pair(self, pair):
    self.pairs.append(pair)
    return self

  def add_structured_vector(self, vec):
    if self.one is not None:
      self.one = self.one + vec
    else:
      self.one = vec
    return self

  def _from(other):
    v = StructuredVectorPairCombination()
    if isinstance(other, int) or isinstance(other, str) or \
       isinstance(other, Expr) or isinstance(other, UnitVector) or \
       isinstance(other, SparseVector) or isinstance(other, PowerVector) or \
       isinstance(other, StructuredVector):
      return v.add_structured_vector(StructuredVector._from(other))
    if isinstance(other, StructuredVectorPair):
      return v.add_pair(other)
    if isinstance(other, tuple) and isinstance(other[0], StructuredVector) and \
       isinstance(other[1], StructuredVector):
      return v.add_pair(StructuredVectorPair(other[0], other[1]))
    if isinstance(other, StructuredVectorPairCombination):
      v.pairs = [pair for pair in other.pairs]
      v.one = other.one
      return v
    raise Exception("Cannot convert %s to StructuredVectorPairCombination" % (type(other)))

  def __add__(self, other):
    if not isinstance(other, StructuredVectorPairCombination):
      other = StructuredVectorPairCombination._from(other)

    ret = StructuredVectorPairCombination()
    ret.pairs = self.pairs + other.pairs
    ret.one = None if self.one is None and other.one is None \
                   else (StructuredVector._from(0) if self.one is None else self.one) + \
                        (StructuredVector._from(0) if other.one is None else other.one)
    return ret

  def __radd__(self, other):
    return self.__add__(other)

  def __neg__(self):
    ret = StructuredVectorPairCombination()
    ret.pairs = [-pair for pair in self.pairs]
    ret.one = None if self.one is None else -self.one
    return ret

  def __sub__(self, other):
    return self.__add__(-other)

  def __rsub__(self, other):
    return self.__neg__().__add__(other)


class NamedVectorPairCombination(CoeffMap):
  def __init__(self):
    super(NamedVectorPairCombination, self).__init__()

  def copy(self):
    return NamedVectorPairCombination._from(self)

  def _from(other):
    v = NamedVectorPairCombination()
    if isinstance(other, int) or isinstance(other, str) or \
       isinstance(other, Expr) or isinstance(other, UnitVector) or \
       isinstance(other, SparseVector) or isinstance(other, PowerVector) or \
       isinstance(other, StructuredVector) or isinstance(other, StructuredVectorPair):
      return v.set("one", StructuredVectorPairCombination._from(other))
    if isinstance(other, StructuredVectorPairCombination):
      return v.set("one", other.copy())
    if isinstance(other, tuple) and isinstance(other[0], NamedVector) and \
       isinstance(other[1], NamedVector):
      return v.set(NamedVectorPair(other[0], other[1]), StructuredVector._from(1))
    if isinstance(other, tuple) and isinstance(other[0], NamedVectorPair) and \
       isinstance(other[1], StructuredVector):
      return v.set(other[0], other[1])
    if isinstance(other, tuple) and isinstance(other[0], NamedVectorPair) and \
       isinstance(other[1], SparseVector):
      return v.set(other[0], StructuredVector._from(other[1]))
    if isinstance(other, NamedVectorPair):
      return v.set(other, StructuredVector._from(1))
    if isinstance(other, NamedVectorPairCombination) or type(other) == CoeffMap:
      for key, value in other.items():
        v._dict[key] = value
      return v
    raise Exception("Cannot convert %s to NamedVectorPairCombination" % (str(other)))

  def __add__(self, other):
    if not isinstance(other, NamedVectorPairCombination):
      other = NamedVectorPairCombination._from(other)

    ret = super(NamedVectorPairCombination, self).__add__(other)
    return NamedVectorPairCombination._from(ret)

  def __radd__(self, other):
    return self.__add__(other)

  def __neg__(self):
    return NamedVectorPairCombination._from(super(NamedVectorPairCombination, self).__neg__())

  def __sub__(self, other):
    return self.__add__(-other)

  def __rsub__(self, other):
    return self.__neg__().__add__(other)

  def generate_vector_combination(self, omega):
    named_vector_structure_pairs = []
    structured_vector_pair_combination = None
    ret = RustBuilder()
    for key, vector_coeff in self.items():
      vector_pair, coeff = vector_coeff
      if key == "one":
        structured_vector_pair_combination = coeff
      elif vector_pair.u is not None and vector_pair.v is not None:
        v = get_named_vector("v")
        to_shift = Symbol(get_name("shiftlength"))
        ret.append(rust_define_vector_poly_mul_shift(
          v, rust_pk(vector_pair.u), rust_pk(vector_pair.v), omega, to_shift
        )).end()
        named_vector_structure_pairs.append((v, coeff.shift(-to_shift)))
      elif vector_pair.u is not None:
        v = get_named_vector("v")
        to_shift = Symbol(get_name("shiftlength"))
        ret.append(rust_define_vector_reverse_omega_shift(
          v, vector_pair.u, omega, to_shift
        )).end()
        named_vector_structure_pairs.append((v, coeff.shift(-to_shift)))
      elif vector_pair.v is not None:
        named_vector_structure_pairs.append((vector_pair.v, coeff))
      else:
        raise Exception("Invalid named vector pair")

    named_power_sparse_tuples = []
    vector_combination = VectorCombination()
    power_power_sparse_tuples = []
    for v, st in named_vector_structure_pairs:
      for key, p_coeff in st.items():
        p, coeff = p_coeff
        if key == "one":
          vector_combination += v * coeff
        else:
          named_power_sparse_tuples.append((v, p, coeff))

    if structured_vector_pair_combination is not None:
      if structured_vector_pair_combination.one is not None:
        vector_combination += structured_vector_pair_combination.one
      for structured_vector_pair in structured_vector_pair_combination.pairs:
        if structured_vector_pair.u is not None and \
           structured_vector_pair.v is not None:
          for left_key, left_p_coeff in structured_vector_pair.u.items():
            left_p, left_coeff = left_p_coeff
            for right_key, right_p_coeff in structured_vector_pair.v.items():
              right_p, right_coeff = right_p_coeff
              if left_key != "one" and right_key != "one":
                coeff = left_coeff * right_coeff # convolution(left_coeff, right_coeff, omega)
                power_power_sparse_tuples.append((left_p, right_p, coeff))
              elif left_key != "one":
                vector_combination += left_p * left_coeff * right_coeff # convolution(left_p * left_coeff, right_coeff, omega)
              elif right_key != "one":
                vector_combination += left_coeff * right_coeff * right_p # convolution(left_coeff, right_coeff * right_p, omega)
              else:
                vector_combination += left_coeff * right_coeff # convolution(left_coeff, right_coeff, omega)

    for v, p, s in named_power_sparse_tuples:
      vec = get_named_vector("v")
      ret.append(rust_define_vector_power_mul(
        vec, rust_pk(v), rust(p.alpha, to_field=True), p.size
      )).end()
      vector_combination += vec * s

    for p1, p2, s in power_power_sparse_tuples:
      v = get_named_vector("v")
      ret.append(rust_define_power_power_mul(
        v, rust(p1.alpha, to_field=True), p1.size, rust(p2.alpha, to_field=True), p2.size)
      ).end()
      vector_combination += v * s

    return ret, vector_combination


def convolution(left, right, omega):
  if isinstance(left, VectorCombination) and isinstance(right, VectorCombination):
    ret = NamedVectorPairCombination()
    # Multiplying vector combinations, named vectors are combined to named vector pairs
    # structured vectors are combined to structured vector pairs
    # the coefficients are convoluted
    for left_key, left_vector_coeff in left.items():
      for right_key, right_vector_coeff in right.items():
        left_vector, left_coeff = left_vector_coeff
        right_vector, right_coeff = right_vector_coeff
        coeff = convolution(left_coeff, right_coeff, omega)
        if left_key == "one" and right_key == "one":
          ret += coeff
        elif left_key != "one" and right_key == "one":
          ret += (NamedVectorPair(left_vector, None), coeff)
        elif left_key == "one" and right_key != "one":
          ret += (NamedVectorPair(None, right_vector), coeff)
        else:
          ret += (NamedVectorPair(left_vector, right_vector), coeff)
    return ret

  if isinstance(left, VectorCombination):
    ret = NamedVectorPairCombination()
    for left_key, left_vector_coeff in left.items():
      left_vector, left_coeff = left_vector_coeff
      coeff = convolution(left_coeff, right, omega)
      if left_key == "one":
        ret += coeff
      else:
        ret += (NamedVectorPair(left_vector, None), coeff)
    return ret

  if isinstance(right, VectorCombination):
    ret = NamedVectorPairCombination()
    for right_key, right_vector_coeff in right.items():
      right_vector, right_coeff = right_vector_coeff
      coeff = convolution(left, right_coeff, omega)
      if left_key == "one":
        ret += coeff
      else:
        ret += (NamedVectorPair(None, right_vector), coeff)
    return ret

  if isinstance(left, StructuredVector) and isinstance(right, StructuredVector):
     return StructuredVectorPair(left.reverse_omega(omega), right)

  return left.reverse_omega(omega) * right


if __name__ == "__main__":
  H = Symbol("H")
  ell = Symbol("ell")
  omega = Symbol("omega")
  vpc = NamedVectorPairCombination._from(
          convolution(StructuredVector._from(PowerVector(1, H)),
                      StructuredVector._from(PowerVector(1, H)), omega)) \
          .generate_vector_combination(omega)

  conv = convolution(PowerVector(1, ell).shift(H), UnitVector(H), omega)
  print(conv.dumps())

