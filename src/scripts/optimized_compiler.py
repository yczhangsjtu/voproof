from vector_symbol import NamedVector, PowerVector, UnitVector, \
    NamedPolynomial, NamedVectorPolynomial, \
    SparseVector, get_name, reset_name_counters, \
    StructuredVector, VectorCombination, get_named_vector, \
    PolynomialCombination, simplify_max_with_hints, \
    get_named_polynomial, PolynomialCommitment, Matrix, \
    rust_pk_vk, rust_vk, convolution, NamedVectorPairCombination
from latex_builder import tex, LaTeXBuilder, AccumulationVector, \
    ExpressionVector, Math, Enumerate, Itemize, \
    add_paren_if_add, Algorithm
import rust_builder
from rust_builder import *
from sympy import Symbol, Integer, UnevaluatedExpr, Expr, Max, simplify, \
    latex, srepr, Add, Mul
from sympy.core.numbers import Infinity
from sympy.abc import alpha, beta, gamma, X, D, S
from os.path import basename

F = Symbol("\\mathbb{F}")
Fstar = Symbol("\\mathbb{F}^*")
sym_i = Symbol("i")


def get_rust_type(expr):
  if isinstance(expr, PolynomialCommitment):
    return "Commitment<E>"
  if isinstance(expr, NamedVector):
    return "Vec<E::Fr>"
  if isinstance(expr, Matrix):
    # Sparse representation of a matrix
    return "(Vec<u64>, Vec<u64>, Vec<E::Fr>)"
  if isinstance(expr, Symbol):
    if str(expr).startswith("W"):
      return "KZGProof<E>"
    else:
      return "E::Fr"
  raise Exception("Unknown rust type for: %s of type %s" %
                  (latex(expr), type(expr)))


class Computes(object):
  def __init__(self, latex_builder, rust_builder, owner=None):
    self.latex_builder = latex_builder
    self.rust_builder = rust_builder
    self.owner = owner

  def dumps(self):
    ret = tex(self.latex_builder)
    if self.owner is not None:
      ret = "\\%s computes %s" % (self.owner, ret)
    return ret

  def dumpr(self):
    return rust(self.rust_builder)


class IndexerComputes(Computes):
  def __init__(self, latex_builder, rust_builder, has_indexer=True):
    super().__init__(latex_builder, rust_builder,
                     "indexer" if has_indexer else None)


class ProverComputes(Computes):
  def __init__(self, latex_builder, rust_builder, has_prover=True):
    super().__init__(latex_builder, rust_builder,
                     "prover" if has_prover else None)


class VerifierComputes(Computes):
  def __init__(self, latex_builder, rust_builder, has_verifier=True):
    super().__init__(latex_builder, rust_builder,
                     "verifier" if has_verifier else None)


class VerifierSendRandomnesses(object):
  def __init__(self, *args):
    self.names = args

  def add_randomnesses(self, *names):
    self.names += names

  def dumps(self):
    return "\\verifier sends %s to \\prover" % \
           Math(",".join([tex(name) for name in self.names])) \
           .sample(Fstar).dumps()


class SubmitVectors(object):
  def __init__(self, submitter, vector, size, rust_size=None):
    rust_size = size if rust_size is None else rust_size
    self.submitter = submitter
    self.vectors = [(vector, size, rust_size)]

  def __len__(self):
    return len(self.vectors)

  def add_vector(self, vector, size, rust_size=None):
    rust_size = size if rust_size is None else rust_size
    self.vectors.append((vector, size, rust_size))

  def dumps(self):
    return "\\%s submits $%s$ to $\\cOV$" % \
           (self.submitter, ",".join([v.dumps()
            for v, size, _ in self.vectors]))


class ProverSubmitVectors(SubmitVectors):
  def __init__(self, vector, size, rust_size=None):
    super().__init__(
        "prover", vector, size, rust_size)


class IndexerSubmitVectors(SubmitVectors):
  def __init__(self, vector, size, rust_size=None):
    super().__init__(
        "indexer", vector, size, rust_size)


class InvokeSubprotocol(object):
  def __init__(self, name, *args):
    self.args = args
    self.name = name

  def dumps(self):
    return "\\prover and \\verifier invokes protocol " \
        "$\\mathsf{%s}$ with inputs %s" % \
           (self.name, ", ".join(["$%s$" % tex(arg) for arg in self.args]))


class IndexerInvokeSubprotocol(object):
  def __init__(self, name, *args):
    self.args = args
    self.name = name

  def dumps(self):
    return "\\indexer invokes the indexer of protocol " \
        "$\\mathsf{%s}$ with inputs %s" % \
           (self.name, ", ".join(["$%s$" % tex(arg) for arg in self.args]))


class SendPolynomials(object):
  def __init__(self, sender, polynomial, degree, rust_degree=None):
    rust_degree = degree if rust_degree is None else rust_degree
    self.sender = sender
    self.polynomials = [(polynomial, degree, rust_degree)]

  def __len__(self):
    return len(self.polynomials)

  def add_polynomial(self, polynomial, degree, rust_degree=None):
    rust_degree = degree if rust_degree is None else rust_degree
    self.polynomials.append((polynomial, degree, rust_degree))

  def dumps(self):
    return "\\%s sends %s to \\verifier" % \
        (self.sender, ", ".join(["$[%s]$ of degree $%s$" % (p.dumps(), tex(degree-1))
                                 for p, degree, rust_degree in self.polynomials]))


class ProverSendPolynomials(SendPolynomials):
  def __init__(self, polynomial, degree, rust_degree):
    super().__init__(
        "prover", polynomial, degree, rust_degree)


class IndexerSendPolynomials(SendPolynomials):
  def __init__(self, polynomial, degree, rust_degree):
    super().__init__(
        "indexer", polynomial, degree, rust_degree)


def _register_rust_functions(self):
  for attr in dir(rust_builder):
    if attr.startswith("rust_line_"):
      f = getattr(rust_builder, attr)
      name = attr[len("rust_line_"):]
      setattr(self, "prover_rust_" + name,
              (lambda f: lambda *args: self.prover_computes_rust(f(*args)))(f))
      setattr(self, "verifier_rust_" + name,
              (lambda f: lambda *args: self.verifier_computes_rust(f(*args)))(f))
      setattr(self, "pp_rust_" + name,
              (lambda f: lambda *args: self.preprocess_rust(f(*args)))(f))


class PublicCoinProtocolExecution(object):
  def __init__(self):
    self.prover_inputs = []
    self.verifier_inputs = []
    self.preprocessings = []
    self.indexer_output_pk = []
    self.indexer_output_vk = []
    self.interactions = []
    _register_rust_functions(self)

  def input_instance(self, arg):
    self.verifier_inputs.append(arg)
    self.prover_inputs.append(arg)

  def input_witness(self, arg):
    self.prover_inputs.append(arg)

  def preprocess(self, latex_builder, rust_builder):
    self.preprocessings.append(
        IndexerComputes(latex_builder, rust_builder))

  def preprocess_rust(self, rust_builder):
    self.preprocess(LaTeXBuilder(), rust_builder)

  def preprocess_latex(self, latex_builder):
    self.preprocess(latex_builder, RustBuilder())

  def preprocess_output_pk(self, expr):
    self.indexer_output_pk.append(expr)

  def preprocess_output_vk(self, expr):
    self.indexer_output_vk.append(expr)

  def prover_computes(self, latex_builder, rust_builder):
    self.interactions.append(ProverComputes(latex_builder, rust_builder))

  def prover_computes_latex(self, latex_builder):
    self.prover_computes(latex_builder, RustBuilder())

  def prover_computes_rust(self, rust_builder):
    self.prover_computes(LaTeXBuilder(), rust_builder)

  def prover_redefine_symbol_rust(self, s, name):
    new_s = Symbol(get_name(name))
    self.prover_rust_define(new_s, s)
    return new_s

  def verifier_computes(self, latex_builder, rust_builder):
    self.interactions.append(VerifierComputes(latex_builder, rust_builder))

  def verifier_computes_rust(self, rust_builder):
    self.verifier_computes(LaTeXBuilder(), rust_builder)

  def verifier_redefine_symbol_rust(self, s, name):
    new_s = Symbol(get_name(name))
    self.verifier_computes_rust(rust_line_define(new_s, s))
    return new_s

  def invoke_subprotocol(self, name, *args):
    self.interactions.append(InvokeSubprotocol(name, *args))

  def verifier_send_randomness(self, *args):
    # If the verifier already sent some randomnesses in the last step,
    # this simply appends to the randomnesses
    # args should be Symbol
    if len(self.interactions) > 0 and \
            isinstance(self.interactions[-1], VerifierSendRandomnesses):
      self.interactions[-1].add_randomnesses(*args)
    else:
      self.interactions.append(VerifierSendRandomnesses(*args))

  def verifier_generate_and_send_rand(self, name):
    ret = Symbol(get_name(name))
    self.verifier_send_randomness(ret)
    return ret


class VOQuerySide(object):
  def __init__(self, a, b):
    self.a = a
    self.b = b

  def dump_vec(v):
    ret = v.dumps()
    if not v.is_atom():
      ret = "\\left(%s\\right)" % ret
    return ret

  def _dumps(self, oper):
    return "%s\\%s %s" % (VOQuerySide.dump_vec(self.a),
                          oper, VOQuerySide.dump_vec(self.b))

  def shifts(self):
    return self.a.shifts() + self.b.shifts()

  def __mul__(self, other):
    return VOQuerySide(self.a * other, self.b)

  def __rmul__(self, other):
    return self.__mul__(other)

  def __neg__(self):
    return VOQuerySide(-self.a, self.b)

  def dumpr_at_index(self, index):
    return rust(rust_mul(
        self.a.dumpr_at_index(index),
        self.b.dumpr_at_index(index)))

  def at_least_one_operand_is_structured(self):
    return (not isinstance(self.a, NamedVector) and
            not isinstance(self.a, VectorCombination)) or \
           (not isinstance(self.b, NamedVector) and
            not isinstance(self.b, VectorCombination))


class VOQuery(object):
  def __init__(self, a, b, c=None, d=None):
    self.left_side = VOQuerySide(a, b)
    if c is not None and d is not None:
      self.right_side = VOQuerySide(c, d)
    else:
      self.right_side = None
    self.one_sided = self.right_side is None

  def dump_left_side(self):
    return self.left_side._dumps(self.oper)

  def dump_right_side(self):
    return self.right_side._dumps(self.oper)

  def dump_sides(self):
    if self.one_sided:
      return "%s\\stackrel{?}{=}\\vec{0}" % self.dump_left_side()
    return "%s\\stackrel{?}{=}%s" % \
           (self.dump_left_side(), self.dump_right_side())

  def dump_difference(self):
    if self.one_sided:
      return self.dump_left_side()
    return rust(rust_minus(self.dump_left_side(), self.dump_right_side()))

  def dumpr_at_index(self, index):
    if self.one_sided:
      return self.left_side.dumpr_at_index(index)
    return rust(rust_minus(
        self.left_side.dumpr_at_index(index),
        self.right_side.dumpr_at_index(index)))

  def dump_hadamard_difference(self):
    tmp, self.oper = self.oper, "circ"
    if self.one_sided:
      ret = self.dump_left_side()
    else:
      ret = "%s-%s" % (self.dump_left_side(), self.dump_right_side())
    self.oper = tmp
    return ret

  def dump_hadamard_difference_with_beta_power(self, beta, i):
    difference = self.dump_hadamard_difference()
    beta_power = beta ** i
    if not self.one_sided or difference.startswith("-"):
      difference = "\\left(%s\\right)" % difference

    if i > 0:
      difference = "%s\\cdot %s" % (latex(beta_power), difference)

    return "$%s$" % difference

  def dumps(self):
    return "\\verifier queries $\\cOV$ to check that $%s$" % self.dump_sides()

  def shifts(self):
    ret = self.left_side.shifts()
    if not self.one_sided:
      ret += self.right_side.shifts()
    return ret


class HadamardQuery(VOQuery):
  def __init__(self, a, b, c=None, d=None):
    super().__init__(a, b, c, d)
    self.oper = "circ"


class InnerProductQuery(VOQuery):
  def __init__(self, a, b, c=None, d=None):
    super().__init__(a, b, c, d)
    self.oper = "cdot"


class VOProtocolExecution(PublicCoinProtocolExecution):
  def __init__(self, vector_size, *args):
    super().__init__()
    self.args = args
    self.vector_size = vector_size
    self.rust_vector_size = None
    self.indexer_vectors = None
    self.hadamards = []
    self.inner_products = []
    self.vector_size_bound = Integer(0)
    self.vector_size_sum = Integer(0)
    self._simplify_max_hints = None

  def simplify_max(self, expr):
    if self._simplify_max_hints is not None:
      return simplify_max_with_hints(expr, self._simplify_max_hints)
    return expr

  def preprocess_vector(self, vector, size):
    if self.indexer_vectors is not None:
      self.indexer_vectors.add_vector(vector, size)
    else:
      self.indexer_vectors = IndexerSubmitVectors(vector, size)

  def run_subprotocol_indexer(self, protocol, *args):
    protocol.preprocess(self, *args)

  def try_prover_redefine_vector_size_rust(self, name, value, piopexec=None):
    if self.rust_vector_size is None:
      executor = self if piopexec is None else piopexec
      self.rust_vector_size = executor.prover_redefine_symbol_rust(
          value, name)

  def try_verifier_redefine_vector_size_rust(self, name, value, piopexec=None):
    if self.rust_vector_size is None:
      executor = self if piopexec is None else piopexec
      self.rust_vector_size = executor.verifier_redefine_symbol_rust(
          value, name)

  def _update_vector_size_bound(self, size):
    self.vector_size_bound = self.simplify_max(
        Max(self.vector_size_bound, size))
    self.vector_size_sum += size

  def prover_submit_vector(self, vector, size, rust_size=None):
    if len(self.interactions) > 0 and \
            isinstance(self.interactions[-1], ProverSubmitVectors):
      self.interactions[-1].add_vector(vector, size, rust_size)
    else:
      self.interactions.append(
          ProverSubmitVectors(vector, size, rust_size))
    self._update_vector_size_bound(size)

  def hadamard_query(self, a, b, c=None, d=None):
    self.hadamards.append(HadamardQuery(a, b, c, d))

  def inner_product_query(self, a, b, c=None, d=None):
    self.inner_products.append(InnerProductQuery(a, b, c, d))

  def run_subprotocol(self, protocol, *args):
    protocol.execute(self, *args)

  def dumps(self):
    ret = Algorithm(self.name)
    if hasattr(self, 'index'):
      ret.index = self.index
    ret.inputs = self.inputs
    ret.checks = self.checks
    for pp in self.preprocessings:
      ret.preprocesses.append(pp)
    if self.indexer_vectors is not None:
      for v, size, _ in self.indexer_vectors.vectors:
        ret.output_pk.append(v)
        ret.output_vk.append(v)
    for interaction in self.interactions:
      ret.interactions.append(interaction)
    for had in self.hadamards:
      ret.interactions.append(had.dumps())
    for inner in self.inner_products:
      ret.interactions.append(inner.dumps())
    return ret.dumps()


class VOProtocol(object):
  def __init__(self, name):
    self.name = name

  def get_named_vector_for_latex(self, arg, default_name, voexec):
    if isinstance(arg, NamedVector):
      return arg
    elif isinstance(arg, VectorCombination) or isinstance(arg, PowerVector) or \
            isinstance(arg, SparseVector) or isinstance(arg, UnitVector) or \
            isinstance(arg, StructuredVector):
      ret = get_named_vector(default_name)
      voexec.prover_computes(Math(ret).assign(arg))
      return ret

    raise Exception("Invalid argument type %s" % type(arg))

  def check_argument_type(self, arg, *classtypes):
    for classtype in classtypes:
      if isinstance(arg, classtype):
        return
    raise Exception("Wrong argument type, expected %s, got %s"
                    % (
                        "/".join([t.__name__ for t in classtypes]),
                        type(arg)
                    ))

  def preprocess(self, voexec, *args):
    raise Exception("Should not call VOProtocol.preprocess directly")

  def execute(self, vopexec, *args):
    raise Exception("Should not call VOProtocol.execute directly")


class EvalQuery(object):
  # name = poly(point)
  def __init__(self, name, point, poly):
    self.point = point
    self.poly = poly
    self.name = name

  def dumps(self):
    return "\\verifier queries $[%s]$ at point $%s$ to obtain $%s$" \
           % (self.poly.dumps(), tex(self.point), tex(self.name))

  def dumps_check(self):
    return "\\verifier queries $[%s]$ at point $%s$ and checks if the response is $%s$" \
           % (self.poly.dumps(), tex(self.point), tex(self.name))


class CombinationCoeffBuilder(object):
  def __init__(self, poly, coeff, latex_builder, rust_builder, shifts=0):
    """The coeff here must be symbol"""
    self.poly = poly
    self.coeff = coeff
    self.latex_builder = latex_builder
    self.rust_builder = rust_builder
    self.shifts = shifts

  def transform_lists_to_builders(self):
    """
    Assume that the latex builder and rust builder are currently lists
    Transform them into Itemize() and rust_define_sum respectively
    """
    self.latex_builder = LaTeXBuilder().start_math().append(self.coeff) \
        .assign().end_math().space("the sum of:") \
        .append(Itemize([Math(item) for item in self.latex_builder])) \
        if len(self.latex_builder) > 1 else \
        Math(self.coeff).assign(self.latex_builder[0])

    self.rust_builder = rust_line_define_sum(
        self.coeff, *self.rust_builder)


class CombinePolynomialComputes(object):
  def __init__(self):
    self.coefficient_items = []
    self.coefficient_rust_items = []
    self.oracle_items = []
    self.poly_latex_items = []
    self.poly_rust_items = []
    self.commit_latex_items = []
    self.commit_rust_items = []


class CombinePolynomial(object):
  def __init__(self, poly, coeff_builders, length):
    self.poly = poly
    self.coeff_builders = coeff_builders
    self.length = length

  def dump_computes(self):
    computes = CombinePolynomialComputes()
    oracle_sum_items, poly_sum_items, commit_sum_items = [], [], []
    poly_sum_rust_items, commit_sum_rust_items = [], []
    latex_one, rust_const = None, None

    for key, coeff_builder in self.coeff_builders.items():
      computes.coefficient_items.append(coeff_builder.latex_builder)
      computes.coefficient_rust_items.append(coeff_builder.rust_builder)
      if key == "one":
        latex_one = latex(coeff_builder.coeff)
        rust_const = rust(coeff_builder.coeff)
        continue

      oracle_sum_items.append("%s\\cdot [%s]" % (
          latex(coeff_builder.coeff), coeff_builder.poly.dumps()))
      commit_sum_items.append("%s\\cdot %s" % (
          latex(coeff_builder.coeff), coeff_builder.poly.to_comm()))
      commit_sum_rust_items.append(rust_vk(coeff_builder.poly.to_comm()))
      commit_sum_rust_items.append(rust(coeff_builder.coeff))
      poly_sum_items.append("%s\\cdot %s" % (
          latex(coeff_builder.coeff), coeff_builder.poly.dumps()))
      poly_sum_rust_items.append(rust(coeff_builder.coeff))
      poly_sum_rust_items.append(
          coeff_builder.poly.dumpr_at_index(sym_i - coeff_builder.shifts))

    computes.poly_rust_items.append(
        rust_line_define_vec_mut(self.poly.to_vec(), rust_expression_vector_i(
            rust_linear_combination_base_zero(poly_sum_rust_items),
            self.length)))

    if "one" in self.coeff_builders:
      coeff = self.coeff_builders["one"].coeff
      latex_one = latex(coeff)
      oracle_sum_items.append(latex_one)
      poly_sum_items.append(latex_one)
      commit_sum_items.append("%s\\cdot \\mathsf{com}(1)" % latex_one)

      rust_const = rust(coeff)
      computes.poly_rust_items.append(
          rust_line_add_to_first_item(self.poly.to_vec(), rust_const))
      computes.commit_rust_items.append(
          rust_line_define_commitment_linear_combination(
              self.poly.to_comm(), "vk", rust_const, *commit_sum_rust_items))
    else:
      computes.commit_rust_items.append(
          rust_line_define_commitment_linear_combination_no_one(
              self.poly.to_comm(), "vk", *commit_sum_rust_items))

    computes.oracle_items.append(
        Math("[%s]" % self.poly.dumps()).assign("+".join(oracle_sum_items)))
    computes.poly_latex_items.append(
        Math("%s" % self.poly.dumps()).assign("+".join(poly_sum_items)))
    computes.commit_latex_items.append(
        Math("%s" % self.poly.to_comm()).assign("+".join(commit_sum_items)))

    return computes


class PIOPExecution(PublicCoinProtocolExecution):
  def __init__(self, *args):
    super().__init__()
    self.args = args
    self.indexer_polynomials = None
    self.eval_queries = []
    self.poly_combines = []
    self.eval_checks = []
    self.prover_polynomials = []
    self.distinct_points = set()
    self.debug_mode = False
    self._symbol_dict = {}
    self._power_poly_dict = {}
    self._auto_vector_dict = {}

  def preprocess_polynomial(self, polynomial, degree, rust_degree=None):
    polynomial._is_preprocessed = True
    if self.indexer_polynomials is not None:
      self.indexer_polynomials.add_polynomial(
          polynomial, degree, rust_degree)
    else:
      self.indexer_polynomials = IndexerSendPolynomials(
          polynomial, degree, rust_degree)

  def prover_send_polynomial(self, polynomial, degree, rust_degree=None):
    if len(self.interactions) > 0 and \
            isinstance(self.interactions[-1], ProverSendPolynomials):
      self.interactions[-1].add_polynomial(
          polynomial, degree, rust_degree)
    else:
      self.interactions.append(ProverSendPolynomials(
          polynomial, degree, rust_degree))

    self.prover_polynomials.append(
        ProverSendPolynomials(polynomial, degree, rust_degree))

  def eval_query(self, name, point, poly):
    self.eval_queries.append(EvalQuery(name, point, poly))
    self.distinct_points.add(tex(point))

  def eval_query_for_possibly_local_poly(self, name, point, poly, vec, size):
    if not vec.local_evaluate:
      self.eval_query(name, point, poly)
      self.prover_rust_define_eval_vector_expression_i(
          name, point, vec.dumpr_at_index(sym_i), size)
    else:
      self.verifier_computes_latex(Math(y).assign(poly.dumps_var(point)))
      self.verifier_rust_define(name, vec.hint_computation(point))

  def combine_polynomial(self, poly, coeff_latex_builders, length):
    self.poly_combines.append(CombinePolynomial(
        poly, coeff_latex_builders, length))

  def eval_check(self, left, point, poly):
    # eval_check is handled differently from eval_query
    # verifier uses eval_query to get the value of f(z)
    # but uses eval_check to check if some known y =? f(z)
    # when compiled to zkSNARK, for each eval query, the prover
    # needs to send the query response y to the verifier
    # before they run the evaluation protocol
    # but for each eval check, the prover doesn't need to
    # thus saving a field element in the zkSNARK proof
    self.eval_checks.append(EvalQuery(left, point, poly))
    self.distinct_points.add(tex(point))

  def _format_string(*args):
    if not isinstance(args[0], str):
      raise Exception("The first argument must be string")
    return ('"%s"' % args[0],) + tuple(rust(arg) for arg in args[1:])

  def pp_debug(self, *args):
    if self.debug_mode:
      self.preprocess_rust(
          rust_builder_macro(
              "println",
              *PIOPExecution._format_string(*args)
          ).end()
      )

  def prover_debug(self, *args):
    if self.debug_mode:
      self.prover_computes_rust(
          rust_builder_macro(
              "println",
              *PIOPExecution._format_string(*args)
          ).end()
      )

  def dumps(self):
    ret = Enumerate()
    for pp in self.preprocessings:
      ret.append(pp.dumps())
    ret.append(self.indexer_polynomials.dumps())
    if len(self.indexer_output_vk) > 0:
      ret.append("\\indexer sends $%s$ to \\verifier"
                 % ",".join([tex(v) for v in self.indexer_output_vk]))
    if len(self.indexer_output_pk) > 0:
      ret.append("\\indexer sends $%s$ to \\prover"
                 % ",".join([tex(p) for p in self.indexer_output_pk]))
    for interaction in self.interactions:
      ret.append(interaction.dumps())
    for query in self.eval_queries:
      ret.append(query.dumps())
    for polycom in self.poly_combines:
      computes = polycom.dump_computes()
      ret.append(VerifierComputes(
          computes.coefficient_items, RustBuilder()).dumps())
      ret.append(VerifierComputes(
          computes.oracle_items, RustBuilder()).dumps())
    for query in self.eval_checks:
      ret.append(query.dumps_check())
    return ret.dumps()


class PIOPFromVOProtocol(object):
  def __init__(self, vo, vector_size, degree_bound):
    self.vo = vo
    self.vector_size = vector_size
    self.degree_bound = degree_bound
    self.debug_mode = False

  def debug(self, info):
    if self.debug_mode:
      print(info)

  def preprocess(self, piopexec, *args):
    voexec = VOProtocolExecution(self.vector_size)
    vec_to_poly_dict = {}
    self.vo.preprocess(voexec, *args)
    piopexec.debug_mode = self.debug_mode
    piopexec.degree_bound = self.degree_bound

    for pp in voexec.preprocessings:
      piopexec.preprocess(pp.latex_builder, pp.rust_builder)
    for vector, size, _ in voexec.indexer_vectors.vectors:
      poly = vector.to_named_vector_poly()
      piopexec.preprocess_polynomial(poly, size)
      vec_to_poly_dict[vector.key()] = poly
      piopexec.pp_debug(
          "vector %s of length {} = \n[{}]" % rust(vector),
          "%s.len()" % rust(vector),
          rust_fmt_ff_vector(vector)
      )
    piopexec.indexer_output_pk = voexec.indexer_output_pk
    piopexec.indexer_output_vk = voexec.indexer_output_vk
    piopexec.reference_to_voexec = voexec
    piopexec.vec_to_poly_dict = vec_to_poly_dict

  def _generate_new_randomizer(self, samples, k):
    randomizer = get_named_vector("delta")
    samples.append([randomizer, k])
    return randomizer

  def _process_prover_submitted_vector(self, piopexec, v, size, rust_size, samples):
    rust_n = piopexec.reference_to_voexec.rust_vector_size
    # Sample the randomizer
    randomizer = self._generate_new_randomizer(samples, 1)
    poly = v.to_named_vector_poly()
    # Zero pad the vector to size n then append the randomizer
    piopexec.prover_computes(
        Math(randomizer).sample(self.Ftoq).comma(
            Math(v)).assign(v).double_bar(randomizer),
        rust_line_redefine_zero_pad_concat_vector(v, rust_n, randomizer))
    piopexec.prover_send_polynomial(
        poly, self.vector_size + self.q, rust_n + self.q)
    # piopexec.prover_rust_define_poly_from_vec(poly, v)
    piopexec.vec_to_poly_dict[v.key()] = poly

    piopexec.prover_debug(
        "vector %s of length {} = \\n[{}]" % rust(v), "%s.len()" % rust(v),
        rust_fmt_ff_vector(v),
    )

  def _process_interactions(self, piopexec, samples):
    voexec = piopexec.reference_to_voexec
    for interaction in voexec.interactions:
      if isinstance(interaction, ProverComputes):
        piopexec.prover_computes(
            interaction.latex_builder, interaction.rust_builder)
      elif isinstance(interaction, VerifierComputes):
        piopexec.verifier_computes(
            interaction.latex_builder, interaction.rust_builder)
      elif isinstance(interaction, VerifierSendRandomnesses):
        piopexec.verifier_send_randomness(*interaction.names)
      elif isinstance(interaction, ProverSubmitVectors):
        """
        Since the value n can be long and complex, define a new symbol in rust
        and put the long expression of n in this new symbol. This rust version
        of symbol should never be used outside rust context
        Must be postponed to here because only now it is guaranteed that all the
        necessary variables that n depends on are defined
        """
        voexec.try_verifier_redefine_vector_size_rust(
            "n", voexec.vector_size, piopexec)
        for v, size, rust_size in interaction.vectors:
          self._process_prover_submitted_vector(
              piopexec, v, size, rust_size, samples)
      else:
        raise ValueError(
            "Interaction of type %s should not appear" % type(interaction))

  """
  Check that the hadamard product of a query is indeed zero
  """

  def _check_hadamard_sides(self, check_individual_hadamard, side1, side2=None):
    if side2 is None:
      side = side1
      check_individual_hadamard.append(rust_check_vector_eq(
          rust_expression_vector_i(
              rust_mul(
                  (side.a * (1/alpha_power)).dumpr_at_index(sym_i),
                  side.b.dumpr_at_index(sym_i)),
              rust_n),
          rust_vec_size(rust_zero(), rust_n),
          "The %d\'th hadamard check is not satisfied" % (i+1)
      )).end()
    else:
      check_individual_hadamard.append(rust_check_expression_vector_eq(
          rust_mul(
              (side1.a * (1/alpha_power)).dumpr_at_index(sym_i),
              side1.b.dumpr_at_index(sym_i)),
          rust_neg(rust_mul(
              (side2.a * (1/alpha_power)).dumpr_at_index(sym_i),
              side2.b.dumpr_at_index(sym_i))),
          rust_n,
          "The %d\'th hadamard check is not satisfied" % (i+1)
      )).end()

  def _process_inner_product(self, piopexec, extended_hadamard,
                             shifts, samples, ignore_in_t, alpha):
    voexec = piopexec.reference_to_voexec
    beta = piopexec.verifier_generate_and_send_rand("beta")
    r = get_named_vector("r")
    rust_n = voexec.rust_vector_size
    n = voexec.vector_size

    for i, inner in enumerate(voexec.inner_products):
      coeff = (beta ** i) * (alpha ** len(voexec.hadamards))
      extended_hadamard.append(coeff * inner.left_side)
      if not inner.one_sided:
        extended_hadamard.append((- coeff) * inner.right_side)
      shifts += inner.shifts()

    piopexec.prover_computes_latex(
        LaTeXBuilder().start_math().append(r).assign().end_math()
                      .space("the sum of:").eol()
                      .append(
            Itemize().append([
                inner.dump_hadamard_difference_with_beta_power(beta, i)
                for i, inner in enumerate(voexec.inner_products)
            ])))

    piopexec.prover_rust_define_expression_vector_i(r,
                                                    rust_power_linear_combination(beta).append([
                                                        inner.dumpr_at_index(
                                                            sym_i)
                                                        for i, inner in enumerate(voexec.inner_products)
                                                    ]), rust_n)

    randomizer = self._generate_new_randomizer(samples, 1)
    rtilde = get_named_vector("r", modifier="tilde")

    """
    tilde{r} is the accumulation vector of r combined with the randomizer
    """
    piopexec.prover_computes_latex(Math(randomizer).sample(self.Ftoq)
                                   .comma(rtilde).assign(AccumulationVector(r.slice("j"), n))
                                   .double_bar(randomizer))
    piopexec.prover_rust_define_concat_vector(
        rtilde,
        rust_accumulate_vector_plus(r),
        randomizer)

    fr = rtilde.to_named_vector_poly()
    # piopexec.prover_rust_define_poly_from_vec(fr, rtilde)

    piopexec.prover_send_polynomial(fr, n + self.q, rust_n + self.q)
    piopexec.vec_to_poly_dict[rtilde.key()] = fr

    alpha_power = alpha ** len(voexec.hadamards)
    extended_hadamard.append((- alpha_power) *
                             VOQuerySide(rtilde - rtilde.shift(1),
                                         PowerVector(1, n, rust_n)))

    extended_hadamard.append((alpha_power * alpha) *
                             VOQuerySide(rtilde, UnitVector(n, rust_n)))

    # This last hadamard check involves only a named vector times
    # a unit vector, it does not contributes to t
    ignore_in_t.add(len(extended_hadamard) - 1)

  def _process_vector_t(self, piopexec, samples, extended_hadamard, ignore_in_t):
    rust_n = piopexec.reference_to_voexec.rust_vector_size
    n = piopexec.reference_to_voexec.vector_size
    max_shift = piopexec.max_shift
    rust_max_shift = piopexec.rust_max_shift

    t = get_named_vector("t")
    randomizer = self._generate_new_randomizer(samples, 1)

    piopexec.prover_computes_latex(LaTeXBuilder().start_math().append(randomizer)
                                   .sample(self.Ftoq).comma(t).assign(randomizer).double_bar().end_math()
                                   .space("the sum of:").eol().append(Itemize().append([
                                       "$%s$" % side._dumps("circ")
                                       for i, side in enumerate(extended_hadamard)
                                       if not i in ignore_in_t])))

    piopexec.prover_rust_define_vec(t, rust_vector_concat(randomizer,
                                                          rust_expression_vector_i(rust_linear_combination_base_zero(*[
                                                              operand.dumpr_at_index(
                                                                  simplify(sym_i + rust_n))
                                                              for i, side in enumerate(extended_hadamard)
                                                              for operand in [side.a, side.b]
                                                              if not i in ignore_in_t
                                                          ]), 2 * self.q + rust_max_shift)))

    tx = t.to_named_vector_poly()
    piopexec.vec_to_poly_dict[t.key()] = tx
    piopexec.prover_send_polynomial(
        tx, 2 * self.q + max_shift, 2 * self.q + rust_max_shift)

    extended_hadamard.append(VOQuerySide(
        -PowerVector(1, max_shift + self.q, rust_max_shift +
                     self.q).shift(n, rust_n),
        t.shift(n - self.q, rust_n - self.q)
    ))

  def _process_extended_hadamards(self, piopexec, samples):
    """
    Although alpha is sent to the prover after the prover sends all the
    vectors except t, this symbol is used in processing the extended hadamard
    queries. So first declare it here.
    """
    alpha = Symbol(get_name('alpha'))
    """
    A list of VO query sides, each is of the form vec{a} circ vec{b}
    together they should sum to zero
    """
    extended_hadamard = []
    """
    Used to records all the shifts appeared in the vectors,
    and finally compute the maximal shift
    """
    shifts = []

    voexec = piopexec.reference_to_voexec
    rust_n = voexec.rust_vector_size
    n = voexec.vector_size

    if self.debug_mode:
      check_individual_hadmard = RustBuilder()

    """
    Some hadamard checks are guaranteed to be zero
    if the prover is honest. In that case, there is no
    need for the honest prover to include those terms
    in t. The hadamard queries that are ignored is stored
    in this set
    """
    ignore_in_t = set()
    for i, had in enumerate(voexec.hadamards):
      alpha_power = alpha ** i

      """
      vec{a} circ vec{b} - vec{c} circ vec{d}
      the right side might be zero (one sided)
      """
      extended_hadamard.append(alpha_power * had.left_side)
      if not had.one_sided:
        extended_hadamard.append((-alpha_power) * had.right_side)
      elif had.left_side.at_least_one_operand_is_structured():
        """
        One sided, and one of the operand is only a structured vector,
        then no need to include this vector in t, because the structured
        vector will be all zero outside the n-window
        """
        ignore_in_t.add(len(extended_hadamard) - 1)

      shifts += had.shifts()

      if self.debug_mode:
        if had.one_sided:
          self._check_hadamard_sides(
              check_individual_hadmard,
              extended_hadamard[-1])
        else:
          self._check_hadamard_sides(
              check_individual_hadmard,
              extended_hadamard[-1],
              extended_hadamard[-2])

    if self.debug_mode:
      piopexec.prover_computes_rust(check_individual_hadmard)

    self.debug("Process inner products")
    if len(voexec.inner_products) > 0:
      self._process_inner_product(piopexec, extended_hadamard,
                                  shifts, samples, ignore_in_t, alpha)

    max_shift = voexec.simplify_max(Max(*shifts))
    rust_max_shift = piopexec.prover_redefine_symbol_rust(
        max_shift, "maxshift")
    piopexec.verifier_send_randomness(alpha)
    piopexec.max_shift = max_shift
    piopexec.rust_max_shift = rust_max_shift

    self.debug("Process vector t")
    self._process_vector_t(
        piopexec, samples, extended_hadamard, ignore_in_t)

    return extended_hadamard, max_shift, rust_max_shift

  def _fix_missing_vector_key(self, vec, piopexec):
    if isinstance(vec, NamedVector) and vec.key() not in piopexec.vec_to_poly_dict:
      """
      This is possible because some named vectors
      might be locally evaluatable, never submitted
      by the prover or the indexer
      """
      if not vec.local_evaluate:
        raise Exception("Some non-local vector is not in the dict: %s"
                        % vec.dumps())
      piopexec.vec_to_poly_dict[vec.key()] = vec.to_named_vector_poly()

  def _pick_the_non_constant(self, key1, key2, vec1, vec2, omega):
    if key2 == "one":
      return vec1, omega / X
    return vec2, X

  def _named_vector_constant_product_omega(
          self, piopexec, coeff, key1, key2, vec1, vec2, omega):
    if key1 == "one" and key2 == "one":  # Constant-Constant
      return "$%s$" % latex(coeff)
    elif key1 == "one" or key2 == "one":  # Named-Constant
      named, named_var = self._pick_the_non_constant(
          key1, key2, vec1, vec2, omega)
      return "$%s\\cdot %s$" % (
          add_paren_if_add(coeff),
          piopexec.vec_to_poly_dict[named.key()].dumps_var(named_var))
    else:  # Named-Named
      return "$%s\\cdot %s\\cdot %s$" % (
          add_paren_if_add(coeff),
          piopexec.vec_to_poly_dict[vec1.key()].dumps_var(omega / X),
          piopexec.vec_to_poly_dict[vec2.key()].dumps_var(X))

  def _increment_h_omega_sum(self, h_omega_sum_check, h_omega_sum, omega, a, b, size):
    h_omega_sum_check.append(h_omega_sum).plus_assign(
        rust_eval_vector_expression_i(omega,
                                      rust_mul(a.dumpr_at_index(
                                          sym_i), b.dumpr_at_index(sym_i)),
                                      rust(size))
    ).end()

  def _increment_vec_sum(self, piopexec, vecsum, a, b):
    piopexec.prover_rust_add_expression_vector_to_vector_i(vecsum,
                                                           rust_mul(a.dumpr_at_index(sym_i), b.dumpr_at_index(sym_i)))

  def _increment_h_check_by_naive_atimesb(self, piopexec, hcheck_vec, a, b, size, omega):
    atimesb_vec_naive = get_named_vector("abnaive")
    piopexec.prover_rust_define_vector_poly_mul(
        atimesb_vec_naive,
        rust_expression_vector_i(a.dumpr_at_index(sym_i), size),
        rust_expression_vector_i(b.dumpr_at_index(sym_i), size),
        omega
    )
    piopexec.prover_rust_add_vector_to_vector(
        hcheck_vec, atimesb_vec_naive)
    return atimesb_vec_naive

  def _computes_atimesb_vec(self, piopexec, atimesb, omega, a, b, size):
    atimesb_computes_rust, atimesb_vector_combination = \
        atimesb.generate_vector_combination(omega)
    piopexec.prover_computes_rust(atimesb_computes_rust)

    atimesb_vec = get_named_vector("atimesb")
    piopexec.prover_computes_rust("// The vector pair here is %s and %s\n" %
                                  (a.dumps(), b.dumps()))
    piopexec.prover_rust_define_expression_vector_i(atimesb_vec,
                                                    atimesb_vector_combination.dumpr_at_index(
                                                        sym_i - size + 1),
                                                    2 * size - 1)

    return atimesb_vec

  def _process_h(self, piopexec, extended_hadamard):
    omega = piopexec.verifier_generate_and_send_rand("omega")
    n = piopexec.reference_to_voexec.vector_size
    rust_n = piopexec.reference_to_voexec.rust_vector_size
    max_shift = piopexec.max_shift
    rust_max_shift = piopexec.rust_max_shift

    hx = get_named_polynomial("h")
    hx_items = Itemize()
    hx_vector_combination = NamedVectorPairCombination()

    if self.debug_mode:
      h_omega_sum = Symbol(get_name('h_osum'))
      h_omega_sum_check = rust_builder_define_mut(
          h_omega_sum, rust_zero()).end()
      vecsum = get_named_vector("sum")
      piopexec.prover_rust_define_mut(vecsum,
                                      rust_vec_size(rust_zero(), rust_n + rust_max_shift + self.q))
      hcheck_vec = get_named_vector("hcheck")
      piopexec.prover_rust_define_mut(hcheck_vec,
                                      rust_vec_size(rust_zero(), (rust_n + rust_max_shift + self.q) * 2 - 1))

    for i, side in enumerate(extended_hadamard):
      self.debug("  Extended Hadamard %d" % (i + 1))
      a = VectorCombination._from(side.a)
      b = VectorCombination._from(side.b)
      atimesb = convolution(a, b, omega)
      hx_vector_combination += atimesb

      """
      Cross term multiplication
      """
      for key1, vec_value1 in a.items():
        vec1, value1 = vec_value1
        for key2, vec_value2 in b.items():
          vec2, value2 = vec_value2

          self._fix_missing_vector_key(vec1, piopexec)
          self._fix_missing_vector_key(vec2, piopexec)
          hx_items.append(self._named_vector_constant_product_omega(piopexec,
                                                                    simplify(value1.to_poly_expr(
                                                                        omega / X) * value2.to_poly_expr(X)),
                                                                    key1, key2, vec1, vec2, omega))

      if self.debug_mode:
        size = rust_n + rust_max_shift + self.q
        self._increment_h_omega_sum(
            h_omega_sum_check, h_omega_sum, omega, a, b, size)
        self._increment_vec_sum(piopexec, vecsum, a, b)
        piopexec.prover_rust_check_vector_eq(
            self._computes_atimesb_vec(
                piopexec, atimesb, omega, a, b, size),
            rust_zero_pad(self._increment_h_check_by_naive_atimesb(
                piopexec, hcheck_vec, a, b, size, omega
            ), 2 * size - 1),
            "The %d'th convolution is incorrect" % (i+1))

    h = get_named_vector("h")
    hxcomputes_rust, h_vec_combination = \
        hx_vector_combination.generate_vector_combination(omega)
    piopexec.prover_computes(LaTeXBuilder()
                             .start_math().append(hx).assign().end_math()
                             .space("the sum of:").eol().append(hx_items),
                             hxcomputes_rust)

    h_degree, h_inverse_degree = n + max_shift + self.q, n + max_shift + self.q
    rust_h_degree = rust_n + rust_max_shift + self.q
    rust_h_inverse_degree = rust_n + rust_max_shift + self.q

    if self.debug_mode:
      h_omega_sum_check.append(rust_assert_eq(
          h_omega_sum, rust_zero())).end()
      piopexec.prover_computes_rust(h_omega_sum_check)
      piopexec.prover_rust_check_vector_eq(vecsum,
                                           rust_vec_size(
                                               rust_zero(), rust_n + max_shift + q),
                                           "sum of hadamards not zero")
      piopexec.prover_rust_define_expression_vector_i(
          h, h_vec_combination.dumpr_at_index(
              sym_i - rust_h_inverse_degree + 1),
          rust_h_degree + rust_h_inverse_degree - 1)
      piopexec.prover_rust_check_vector_eq(
          h, hcheck_vec, "h is not expected")

    return h, hx, h_vec_combination, h_degree, h_inverse_degree, \
        rust_h_degree, rust_h_inverse_degree, omega

  def _split_h(self, piopexec, h, hx, h_vec_combination,
               h_degree, h_inverse_degree, rust_h_degree, rust_h_inverse_degree):
    h1 = get_named_vector("h")
    h2 = get_named_vector("h")

    piopexec.prover_rust_define_expression_vector_i(h1,
                                                    h_vec_combination.dumpr_at_index(
                                                        sym_i - rust_h_inverse_degree + 1),
                                                    rust_h_inverse_degree - 1)
    piopexec.prover_rust_define_expression_vector_i(h2,
                                                    h_vec_combination.dumpr_at_index(
                                                        sym_i + 1),
                                                    rust_h_degree - 1)

    if self.debug_mode:
      piopexec.prover_rust_check_vector_eq(h,
                                           rust_vector_concat(
                                               h1, rust_vec(rust_zero()), h2),
                                           "h != h1 || 0 || h2")
      piopexec.prover_rust_assert_eq(
          h_vec_combination.dumpr_at_index(1), rust_zero())

    h1x = h1.to_named_vector_poly()
    h2x = h2.to_named_vector_poly()
    piopexec.prover_computes_latex(Math(h1x).assign(hx).dot(X ** self.degree_bound)
                                   .append("\\bmod").append(X ** self.degree_bound))
    piopexec.prover_computes_latex(Math(h2x).assign("\\frac{%s}{X}" % hx.dumps_var(X))
                                   .minus("X^{%s}\\cdot %s" % (latex(-self.degree_bound-1), h1x.dumps_var(X))))

    piopexec.prover_send_polynomial(h1x, self.degree_bound)
    piopexec.prover_send_polynomial(h2x, h_degree - 1, rust_h_degree - 1)

    return h1, h2, h1x, h2x

  def _collect_named_vec_in_left_operands(self, extended_hadamard):
    ret = {}
    for had in extended_hadamard:
      if isinstance(had.a, NamedVector):
        ret[had.a.key()] = had.a
      elif isinstance(had.a, VectorCombination):
        had.a.dump_named_vectors(ret)
    return ret

  def _homomorphic_check(self, piopexec, extended_hadamard, h1, h2, h1x, h2x, omega,
                         rust_h_inverse_degree, h_degree, rust_max_shift):
    z = piopexec.verifier_generate_and_send_rand("z")
    z0 = omega/z
    rust_n = piopexec.reference_to_voexec.rust_vector_size
    rust_max_shift = piopexec.rust_max_shift

    self.debug("Collect named vectors inside left operands")
    left_named_vectors = self._collect_named_vec_in_left_operands(
        extended_hadamard)

    self.debug("Make evaluation queries")
    query_results = {}
    for key, vec in left_named_vectors.items():
      y = Symbol(get_name("y"))
      query_results[key] = y
      piopexec.eval_query_for_possibly_local_poly(
          y, z0, piopexec.vec_to_poly_dict[key], vec, rust_n + self.q)

    self.debug("Compute gx")
    self._combine_polynomials_in_right_operands(
        piopexec, extended_hadamard, z, z0, query_results,
        h1x, h2x, rust_h_inverse_degree, rust_n + rust_max_shift + self.q)

  def _add_to_naive_g(self, piopexec, vec, coeff=None):
    value = vec_or_value.dumpr_at_index(sym_i)
    value = value if coeff is None else rust_mul(value, coeff)
    piopexec.prover_rust_add_expression_vector_to_vector_i(
        piopexec.naive_g, value)

  def _populate_coeff_builder_by_hadamard_query(
          self, piopexec, side, coeff_builders, z0, z, query_results, size):
    """
    assume side.a = f_i(X), side.b = g_i(X)
    then this query branch contributes a f_i(omega/z) * g_i(X) to the final polynomial g(X)
    to compute f_i(omega/z), split f_i(X) into linear combination of named polynomials
    where the coefficients are structured polynomials, i.e.,
    f_i(omega/z) = s_1(omega/z) p_1(omega/z) + ... + s_k(omega/z) p_k(omega/z) + s_0(omega/z)
    """
    a = VectorCombination._from(side.a)
    # now multiplier should equal f_i(omega/z). if zero, then ignore this term
    multiplier = simplify(sum([
        vec_value[1].to_poly_expr(
            z0) * (1 if key == "one" else query_results[key])
        for key, vec_value in a.items()]))

    # check that multiplier = f_i(omega/z)
    if self.debug_mode:
      piopexec.prover_rust_assert_eq(
          multiplier,
          rust_eval_vector_expression_i(
              z0, a.dumpr_at_index(sym_i),
              rust_n + rust_max_shift + q))

    if multiplier == 0:
      return
    b = VectorCombination._from(side.b) * multiplier

    # The naive way to compute f_i(omega/z) g_i(X), is to directly dump g_i(X)
    # coefficients on [1..n+max_shift+q], multiplied by the multiplier
    if self.debug_mode:
      self._add_to_naive_g(piopexec, b)

    # Now decompose g_i(X), i.e., the right side of this Extended Hadamard query
    # multiply every coefficient by the multiplier f_i(omega/z)
    # then evaluate the coefficient at z
    for key, vec_value in b.items():
      vec, value = vec_value
      rust_value = simplify(value.to_poly_expr_rust(z))
      value = simplify(value.to_poly_expr(z))
      if value == 0 or rust_value == 0:
        raise Exception("value should not be zero")

      poly = "one" if key == "one" else piopexec.vec_to_poly_dict[vec.key(
      )]
      value = latex(value)

      if isinstance(vec, NamedVector) and vec.local_evaluate:
        # In case it is locally evaluatable polynomial, this term should be
        # regarded as part of the constant, instead of a polynomial. Let the verifier
        # locally evaluate this polynomial at z
        key, value, poly = "one", "%s\\cdot %s" % (
            value, poly.dumps_var(z)), "one"
        rust_value = rust_mul(rust_value, vec.hint_computation(z))

      # If this polynomial (or constant) has not been handled before, initialize
      # it with empty list and a new symbol for the coefficient
      # We temporarily use list here, because the format depends on whether
      # this list size is > 1
      if key not in coeff_builders:
        coeff_builders[key] = CombinationCoeffBuilder(
            poly, Symbol(get_name("c")), [], [])

      coeff_builder = coeff_builders[key]
      coeff_builder.latex_builder.append(value)
      coeff_builder.rust_builder.append(rust_value)

  def _check_hz(self, z0, z, extended_hadamard, size, h, rust_h_inverse_degree):
    # Check that h(z) = sum_i f_i(omega/z) g_i(z) z^{n+maxshift+q}
    lc = rust_linear_combination_base_zero()
    for had in extended_hadamard:
      lc.append(rust_eval_vector_expression_i(z0,
                                              VectorCombination._from(had.a).dumpr_at_index(sym_i), size))
      lc.append(rust_eval_vector_expression_i(z,
                                              VectorCombination._from(had.b).dumpr_at_index(sym_i), size))
    piopexec.prover_rust_assert_eq(lc,
                                   rust_mul(rust_eval_vector_as_poly(h, z),
                                            z**(-(rust_h_inverse_degree-1))))

  def _combine_polynomials_in_right_operands(
          self, piopexec, extended_hadamard, z, z0,
          query_results, h1x, h2x, rust_h_inverse_degree, size):

    if self.debug_mode:
      naive_g = get_named_vector("naive_g")
      # Pass this variable to the zkSNARK, because g has not been computed, cannot
      # make the comparison in the PIOP level.
      piopexec.naive_g = naive_g
      piopexec.prover_rust_define_vec_mut(naive_g,
                                          rust_vec_size(rust_zero(), size))

    # map: key -> (poly, Symbol(coeff), latex_builder, rust_builder)
    coeff_builders = {}
    # 1. The part contributed by the extended hadamard query
    for i, side in enumerate(extended_hadamard):
      self.debug("  Extended Hadamard %d" % (i + 1))
      self._populate_coeff_builder_by_hadamard_query(
          piopexec, side, coeff_builders, z0, z, query_results, size)

    # 2. The part contributed by h1(X) and h2(X)
    # h1(X) is committed aligned to the right boundary of the universal parameters
    # so we should additionally multiply a power of z to it when computing g(X)
    coeff_builders[h1x.key()] = CombinationCoeffBuilder(
        h1x, Symbol(get_name("c")),
        [- z ** (-self.degree_bound)], [- z ** (-self.degree_bound)],
        self.degree_bound - (rust_h_inverse_degree - 1))

    coeff_builders[h2x.key()] = CombinationCoeffBuilder(
        h2x, Symbol(get_name("c")), [- z], [- z], 0)

    if self.debug_mode:
      self._add_to_naive_g(piopexec, h1, -z**(-(h_inverse_degree-1)))
      self._add_to_naive_g(piopexec, h2, -z)
      self._check_hz(z0, z, extended_hadamard,
                     size, h, rust_h_inverse_degree)

    # Transform the lists into latex and rust builders
    for key, coeff_builder in coeff_builders.items():
      coeff_builder.transform_lists_to_builders()

    gx = get_named_polynomial("g")
    piopexec.combine_polynomial(gx, coeff_builders, self.degree_bound)
    piopexec.eval_check(0, z, gx)

  def execute(self, piopexec, *args):
    voexec = piopexec.reference_to_voexec
    self.q = Integer(1)
    self.Ftoq = UnevaluatedExpr(F ** self.q)

    samples = rust_sample_randomizers()
    piopexec.prover_computes_rust(RustBuilder(samples).end())

    self.debug("Executing VO protocol")
    self.vo.execute(voexec, *args)
    piopexec.prover_inputs = voexec.prover_inputs
    piopexec.verifier_inputs = voexec.verifier_inputs

    self.debug("Process interactions")
    self._process_interactions(piopexec, samples)

    self.debug("Prepare extended hadamard")
    extended_hadamard, max_shift, rust_max_shift = \
        self._process_extended_hadamards(piopexec, samples)

    self.debug("Process polynomial h")
    h, hx, h_vec_combination, h_degree, h_inverse_degree, \
        rust_h_degree, rust_h_inverse_degree, omega = \
        self._process_h(piopexec, extended_hadamard)
    piopexec.max_degree = h_degree - 1

    """
    Split h into two halves
    """
    self.debug("Compute h1 and h2")
    h1, h2, h1x, h2x = self._split_h(piopexec, h, hx, h_vec_combination,
                                     h_degree, h_inverse_degree, rust_h_degree, rust_h_inverse_degree)

    """
    Here we assume that the underlying polynomial commitment scheme is
    homomorphic. In that case, the prover only needs to open the polynomials
    involved in all the left operands of the Hadamard queries and the verifier
    can later merge the commitments of polynomials involved in right operands
    linearly.
    """
    self.debug("Verifier's turn")
    self._homomorphic_check(piopexec, extended_hadamard, h1, h2, h1x, h2x, omega,
                            rust_h_inverse_degree, h_degree, rust_max_shift)


class ZKSNARK(object):
  def __init__(self):
    self.indexer_computations = []
    self.prover_computations = []
    self.verifier_computations = []
    self.vk = []
    self.pk = []
    self.proof = []
    self.debug_mode = False
    _register_rust_functions(self)

  def preprocess(self, latex_builder, rust_builder):
    self.indexer_computations.append(
        IndexerComputes(latex_builder, rust_builder, has_indexer=False))

  def preprocess_output_vk(self, expr):
    self.vk.append(expr)

  def preprocess_output_pk(self, expr):
    self.pk.append(expr)

  def prover_computes(self, latex_builder, rust_builder):
    if isinstance(latex_builder, str):
      raise Exception("latex_builder cannot be str: %s" % latex_builder)
    self.prover_computations.append(
        ProverComputes(latex_builder, rust_builder, False))

  def prover_computes_latex(self, latex_builder):
    self.prover_computes(latex_builder, RustBuilder())

  def prover_computes_rust(self, rust_builder):
    self.prover_computes(LaTeXBuilder(), rust_builder)

  def verifier_computes(self, latex_builder, rust_builder):
    self.verifier_computations.append(
        VerifierComputes(latex_builder, rust_builder, False))

  def verifier_computes_latex(self, latex_builder):
    self.verifier_computes(latex_builder, RustBuilder())

  def verifier_computes_rust(self, rust_builder):
    self.verifier_computes(LaTeXBuilder(), rust_builder)

  def prover_verifier_computes(self, latex_builder, rust_builder):
    self.prover_computes(latex_builder, rust_builder)
    self.verifier_computes(latex_builder, rust_builder)

  def prover_verifier_computes_latex(self, latex_builder):
    self.prover_computes_latex(latex_builder)
    self.verifier_computes_latex(latex_builder)

  def prover_verifier_computes_rust(self, rust_builder):
    self.prover_computes_rust(rust_builder)
    self.verifier_computes_rust(rust_builder)

  def dump_indexer(self):
    enum = Enumerate()
    for computation in self.indexer_computations:
      enum.append(computation.dumps())
    itemize = Itemize()
    itemize.append("$\\mathsf{pk}:=(%s)$" %
                   ",".join([tex(v) for v in self.vk]))
    itemize.append("$\\mathsf{vk}:=(%s)$" % ",".join(
        [tex(p) for p in self.pk] + [tex(v) for v in self.vk]))
    enum.append("Output\n" + itemize.dumps())
    return enum.dumps()

  def dump_indexer_rust(self):
    return "".join(
        [computation.dumpr() for computation in self.indexer_computations])

  def dump_prover(self):
    enum = Enumerate()
    for computation in self.prover_computations:
      enum.append(computation.dumps())
    enum.append("Output $\\pi:=\\left(%s\\right)$" %
                ",".join(tex(p) for p in self.proof))
    return enum.dumps()

  def dump_prover_rust(self):
    return "".join([computation.dumpr() for computation in self.prover_computations])

  def dump_verifier(self):
    enum = Enumerate()
    for computation in self.verifier_computations:
      enum.append(computation.dumps())
    return enum.dumps()

  def dump_proof_init(self):
    return ("\n" + " " * 8).join(["let %s = proof.%s;" % (rust(item), rust(item))
                                  for item in self.proof])

  def dump_verifier_rust(self):
    return self.dump_proof_init() + \
        "".join([computation.dumpr()
                 for computation in self.verifier_computations])

  def dump_definition(self, items):
    return "\n    ".join([
        "pub %s: %s," % (rust(item), get_rust_type(item))
        for item in items])

  def dump_construction(self, items):
    return ("\n" + " " * 12).join([
        "%s: %s," % (rust(item), rust(item))
        for item in items])

  def dump_vk_definition(self):
    return self.dump_definition(self.vk)

  def dump_pk_definition(self):
    return self.dump_definition(self.pk)

  def dump_proof_definition(self):
    return self.dump_definition(self.proof)

  def dump_vk_construction(self):
    return self.dump_construction(self.vk)

  def dump_pk_construction(self):
    return self.dump_construction(self.pk)

  def dump_proof_construction(self):
    return self.dump_construction(self.proof)


class ZKSNARKFromPIOPExecKZG(ZKSNARK):
  def __init__(self, piopexec):
    super().__init__()
    self.debug_mode = piopexec.debug_mode
    self.process_piopexec(piopexec)

  def _process_indexer_polynomial(self, poly, degree, rust_degree):
    self.preprocess(Math(poly.to_comm()).assign(
        "\\mathsf{com}\\left(%s, \\mathsf{srs}\\right)" % poly.dumps()),
        rust_line_define_commit_vector(poly.to_comm(), poly.vector, rust_degree))
    self.preprocess_output_vk(poly.to_comm())
    self.transcript.append(poly.to_comm())

  def _process_piopexec_indexer(self, piopexec):
    for preprocess in piopexec.preprocessings:
      self.preprocess(preprocess.latex_builder, preprocess.rust_builder)

    for poly, degree, rust_degree in piopexec.indexer_polynomials.polynomials:
      self._process_indexer_polynomial(poly, degree, rust_degree)

    for p in piopexec.indexer_output_pk:
      self.preprocess_output_pk(p)

    for v in piopexec.indexer_output_vk:
      self.preprocess_output_vk(v)
      self.transcript.append(v)

  def _generate_randomness_from_hashes(self, names):
    for i, r in enumerate(names):
      self.prover_verifier_computes_latex(
          Math(r).assign("\\mathsf{H}_{%d}(%s)"
                         % (i+1, ",".join([tex(x) for x in self.transcript]))))
      self.prover_rust_get_randomness_from_hash(
          r, to_field(i+1), *[rust_pk_vk(x) for x in self.transcript])
      self.verifier_rust_get_randomness_from_hash(
          r, to_field(i+1), *[rust_vk(x) for x in self.transcript])

  def _process_prover_send_polynomials(self, polynomials):
    for poly, degree, rust_degree in polynomials:
      if not isinstance(poly, NamedVectorPolynomial):
        raise Exception(
            "Unrecognized polynomial type: %s" % type(poly))
      self.prover_computes_latex(Math(poly.to_comm()).assign(
          "\\mathsf{com}\\left(%s, \\mathsf{srs}\\right)"
          % (poly.dumps())))
      self.prover_rust_define_commit_vector_with_pk(
          poly.to_comm(), poly.vector, rust_degree)
      self.transcript.append(poly.to_comm())
      self.proof.append(poly.to_comm())

  def _process_piopexec_interactions(self, piopexec):
    for interaction in piopexec.interactions:
      if isinstance(interaction, ProverComputes):
        self.prover_computes(
            interaction.latex_builder, interaction.rust_builder)
      elif isinstance(interaction, VerifierComputes):
        self.prover_computes(
            interaction.latex_builder, interaction.rust_builder)
        self.verifier_computes(
            interaction.latex_builder, interaction.rust_builder)
      elif isinstance(interaction, VerifierSendRandomnesses):
        self._generate_randomness_from_hashes(interaction.names)
      if isinstance(interaction, ProverSendPolynomials):
        self._process_prover_send_polynomials(interaction.polynomials)

  def _process_piopexec_computes_query_results(self, piopexec):
    self.prover_computes_latex(Math(",".join(["%s:=%s" %
                                              (tex(query.name), tex(
                                                  query.poly.dumps_var(query.point)))
                                              for query in piopexec.eval_queries])))
    self.proof += [query.name for query in piopexec.eval_queries]

  def _process_polynomial_combination(self, piopexec):
    for poly_combine in piopexec.poly_combines:
      computes = poly_combine.dump_computes()
      for item in computes.coefficient_items:
        self.prover_computes_latex(item)
        self.verifier_computes_latex(item)
      for rust_item in computes.coefficient_rust_items:
        self.prover_computes_rust(rust_item)
        self.verifier_computes_rust(rust_item)
      for item in computes.poly_latex_items:
        self.prover_computes_latex(item)
      for item in computes.poly_rust_items:
        self.prover_computes_rust(item)
      for item in computes.commit_latex_items:
        self.prover_computes_latex(item)
        self.verifier_computes_latex(item)
      for item in computes.commit_rust_items:
        self.prover_computes_rust(item)
        self.verifier_computes_rust(item)

      self.transcript.append(poly_combine.poly.to_comm())

      if piopexec.debug_mode:
        self.prover_rust_assert_eq(
            poly_combine.poly.to_comm(),
            rust_commit_vector_with_pk(
                poly_combine.poly.to_vec(),
                poly_combine.length))

  def _generate_points_poly_dict(self, queries):
    points_poly_dict = {}
    for query in queries:
      if isinstance(query.poly, NamedVectorPolynomial):
        self.prover_rust_define_poly_from_vec(
            query.poly, query.poly.vector)
      elif isinstance(query.poly, NamedPolynomial):
        self.prover_rust_define_poly_from_vec(
            query.poly, query.poly.to_vec())

      key = latex(query.point)
      if key not in points_poly_dict:
        points_poly_dict[key] = []
      points_poly_dict[key].append(query)
    return points_poly_dict
    
  def _parepare_for_kzg_open(self, points_poly_dict, transcript):
    open_proof, open_points, query_tuple_lists, ffs, fcomms, fvals = [
        [] for i in range(6)]
    for point, queries in points_poly_dict.items():
      open_proof.append(Symbol(get_name("W")))
      open_points.append(queries[0].point)
      transcript.append(queries[0].point)
      query_tuple_lists.append([(query.poly.to_comm(),
                                 query.name, query.poly.dumps())
                                for query in queries])
      for query in queries:
        if not isinstance(query.name, int):
          transcript.append(query.name)
        else:
          # Only make this check when the query result is an expected constant
          self.prover_rust_check_poly_eval(
              query.poly,
              queries[0].point,
              rust_zero() if query.name == 0
              else query.name,
              "g does not evaluate to 0 at z")

      ffs.append([rust(query.poly) for query in queries])
      fcomms.append([rust_vk(query.poly.to_comm()) for query in queries])
      fvals.append([rust_zero() if query.name == 0 else query.name
                    for query in queries])

    fs, gs = ffs
    fcomms, gcomms = fcomms
    fvals, gvals = fvals
    return open_proof, open_points, query_tuple_lists, fs, gs, fcomms, gcomms, fvals, gvals

  def process_piopexec(self, piopexec):
    transcript = [x for x in piopexec.verifier_inputs]
    self.transcript = transcript
    self._process_piopexec_indexer(piopexec)
    self._process_piopexec_interactions(piopexec)
    self._process_piopexec_computes_query_results(piopexec)
    self._process_polynomial_combination(piopexec)

    queries = piopexec.eval_queries + piopexec.eval_checks

    if piopexec.debug_mode:
      z = [query.point for query in queries if query.name == 0][0]
      naive_g = piopexec.naive_g
      self.prover_rust_define_poly_from_vec(
          naive_g.to_named_vector_poly(), naive_g)
      self.prover_rust_check_poly_eval(
          naive_g.to_named_vector_poly(),
          z,
          rust_zero(),
          "naive g does not evaluate to 0 at z")

    points_poly_dict = self._generate_points_poly_dict(queries)
    open_proof, open_points, query_tuple_lists, fs, gs, fcomms, gcomms, fvals, gvals = self._parepare_for_kzg_open(points_poly_dict, transcript)

    self.proof += open_proof

    proof_str = ",".join(tex(p) for p in open_proof)
    open_computation = Math("\\left(%s\\right)" % proof_str)
    open_computation.assign("\\mathsf{open}")
    lists = "\\\\\n".join([("\\{%s\\}," % (
                            ",".join([("%s\\left(%s,%s,%s\\right)" %
                                       ("\\\\\n" if i % 3 == 0 and i > 0 else "",
                                        tex(query[0]), tex(query[1]), tex(query[2])))
                                      for i, query in enumerate(tuple_list)])
                            )) for tuple_list in query_tuple_lists])
    points = "\\left\\{%s\\right\\}" % (
        ",".join(tex(p) for p in open_points))
    array = "\\begin{array}{l}\n%s\\\\\n%s\n\\end{array}" % (lists, points)
    open_computation.paren(array)

    open_computation_rust = RustBuilder()
    open_computation_rust.append(rust_define("fs", rust_vec(fs))).end()
    open_computation_rust.append(rust_define("gs", rust_vec(gs))).end()

    compute_zs = RustBuilder()
    compute_zs.append(rust_define("z1", open_points[0])).end()
    compute_zs.append(rust_define("z2", open_points[1])).end()

    compute_rand_xi = RustBuilder()
    compute_rand_xi.append(rust_line_get_randomness_from_hash(
        "rand_xi", to_field(1), *[rust_vk(x) for x in transcript]
    ))
    compute_rand_xi.append(rust_line_get_randomness_from_hash(
        "rand_xi_2", to_field(2), *[rust_vk(x) for x in transcript]
    ))

    lists = "\\\\\n".join([("\\left\\{%s\\right\\}," % (
                            ",".join([("\\left(%s,%s\\right)" %
                                       (tex(query[0]), tex(query[1])))
                                      for query in tuple_list])
                            )) for tuple_list in query_tuple_lists])
    array = "\\begin{array}{l}\n%s\\\\\n%s\n\\left\\{%s\\right\\},[x]_2\\end{array}" \
            % (lists, points, proof_str)
    verify_computation = Math("\\mathsf{vrfy}").paren(array).equals(1)

    verify_computation_rust = RustBuilder()
    verify_computation_rust.append(rust_define(
        "f_commitments", rust_vec(fcomms))).end()
    verify_computation_rust.append(rust_define(
        "g_commitments", rust_vec(gcomms))).end()
    verify_computation_rust.append(
        rust_define("f_values", rust_vec(fvals))).end()
    verify_computation_rust.append(
        rust_define("g_values", rust_vec(gvals))).end()

    self.prover_computes(open_computation, open_computation_rust)
    self.prover_computes_rust(compute_rand_xi)
    self.prover_computes_rust(compute_zs)
    self.verifier_computes_rust(compute_zs)
    self.verifier_computes_rust(compute_rand_xi)
    self.verifier_computes(verify_computation, verify_computation_rust)
