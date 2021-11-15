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
  raise Exception("Unknown rust type for: %s of type %s" % (latex(expr), type(expr)))

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
    super(IndexerComputes, self).__init__(latex_builder, rust_builder,
                                          "indexer" if has_indexer else None)


class ProverComputes(Computes):
  def __init__(self, latex_builder, rust_builder, has_prover=True):
    super(ProverComputes, self).__init__(latex_builder, rust_builder,
                                         "prover" if has_prover else None)


class VerifierComputes(Computes):
  def __init__(self, latex_builder, rust_builder, has_verifier=True):
    super(VerifierComputes, self).__init__(latex_builder, rust_builder,
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
  def __init__(self, submitter, vector, size):
    self.submitter = submitter
    self.vectors = [(vector, size)]

  def __len__(self):
    return len(self.vectors)

  def add_vector(self, vector, size):
    self.vectors.append((vector, size))

  def dumps(self):
    return "\\%s submits $%s$ to $\\cOV$" % \
           (self.submitter, ",".join([v.dumps() for v, size in self.vectors]))


class ProverSubmitVectors(SubmitVectors):
  def __init__(self, vector, size):
    super(ProverSubmitVectors, self).__init__("prover", vector, size)


class IndexerSubmitVectors(SubmitVectors):
  def __init__(self, vector, size):
    super(IndexerSubmitVectors, self).__init__("indexer", vector, size)


class InvokeSubprotocol(object):
  def __init__(self, name, *args):
    self.args = args
    self.name = name

  def dumps(self):
    return "\\prover and \\verifier invokes protocol $\\mathsf{%s}$ with inputs %s" % \
           (self.name, ", ".join(["$%s$" % tex(arg) for arg in self.args]))


class IndexerInvokeSubprotocol(object):
  def __init__(self, name, *args):
    self.args = args
    self.name = name

  def dumps(self):
    return "\\indexer invokes the indexer of protocol $\\mathsf{%s}$ with inputs %s" % \
           (self.name, ", ".join(["$%s$" % tex(arg) for arg in self.args]))


class SendPolynomials(object):
  def __init__(self, sender, polynomial, degree):
    self.sender = sender
    self.polynomials = [(polynomial, degree)]

  def __len__(self):
    return len(self.polynomials)

  def add_polynomial(self, polynomial, degree):
    self.polynomials.append((polynomial, degree))

  def dumps(self):
    return "\\%s sends %s to \\verifier" % (self.sender,
           ", ".join(["$[%s]$ of degree $%s$" % (p.dumps(), tex(degree-1))
                      for p, degree in self.polynomials]))


class ProverSendPolynomials(SendPolynomials):
  def __init__(self, polynomial, degree):
    super(ProverSendPolynomials, self).__init__("prover", polynomial, degree)


class IndexerSendPolynomials(SendPolynomials):
  def __init__(self, polynomial, degree):
    super(IndexerSendPolynomials, self).__init__("indexer", polynomial, degree)


class PublicCoinProtocolExecution(object):
  def __init__(self):
    self.prover_inputs = []
    self.verifier_inputs = []
    self.preprocessings = []
    self.indexer_output_pk = []
    self.indexer_output_vk = []
    self.prover_preparations = []
    self.verifier_preparations = []
    self.interactions = []
    self.verifier_computations = []

  def input_instance(self, arg):
    self.verifier_inputs.append(arg)
    self.prover_inputs.append(arg)

  def input_witness(self, arg):
    self.prover_inputs.append(arg)

  def preprocess(self, latex_builder, rust_builder):
    self.preprocessings.append(IndexerComputes(latex_builder, rust_builder))

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

  def prover_prepare(self, latex_builder, rust_builder):
    self.prover_preparations.append(ProverComputes(latex_builder, rust_builder))

  def verifier_computes(self, latex_builder, rust_builder):
    self.verifier_computations.append(VerifierComputes(latex_builder, rust_builder))

  def verifier_prepare(self, latex_builder, rust_builder):
    self.verifier_preparations.append(VerifierComputes(latex_builder, rust_builder))

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
    return "(%s)*(%s)" % (
        self.a.dumpr_at_index(index),
        self.b.dumpr_at_index(index))


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
    return "%s-%s" % (self.dump_left_side(), self.dump_right_side())

  def dumpr_at_index(self, index):
    if self.one_sided:
      return self.left_side.dumpr_at_index(index)
    return "(%s)-(%s)" % (
        self.left_side.dumpr_at_index(index),
        self.right_side.dumpr_at_index(index))

  def dump_hadamard_difference(self):
    tmp, self.oper = self.oper, "circ"
    if self.one_sided:
      ret = self.dump_left_side()
    else:
      ret = "%s-%s" % (self.dump_left_side(), self.dump_right_side())
    self.oper = tmp
    return ret

  def dumps(self):
    return "\\verifier queries $\\cOV$ to check that $%s$" % self.dump_sides()

  def shifts(self):
    ret = self.left_side.shifts()
    if not self.one_sided:
      ret += self.right_side.shifts()
    return ret


class HadamardQuery(VOQuery):
  def __init__(self, a, b, c=None, d=None):
    super(HadamardQuery, self).__init__(a, b, c, d)
    self.oper = "circ"


class InnerProductQuery(VOQuery):
  def __init__(self, a, b, c=None, d=None):
    super(InnerProductQuery, self).__init__(a, b, c, d)
    self.oper = "cdot"


class VOProtocolExecution(PublicCoinProtocolExecution):
  def __init__(self, vector_size, *args):
    super(VOProtocolExecution, self).__init__()
    self.args = args
    self.vector_size = vector_size
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

  def _update_vector_size_bound(self, size):
    self.vector_size_bound = self.simplify_max(Max(self.vector_size_bound, size))
    self.vector_size_sum += size

  def prover_submit_vector(self, vector, size):
    if len(self.interactions) > 0 and \
      isinstance(self.interactions[-1], ProverSubmitVectors):
      self.interactions[-1].add_vector(vector, size)
    else:
      self.interactions.append(ProverSubmitVectors(vector, size))
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
      for v, size in self.indexer_vectors.vectors:
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

class CombinePolynomial(object):
  def __init__(self, poly, coeff_builders, length):
    self.poly = poly
    self.coeff_builders = coeff_builders
    self.length = length

  def dump_items(self, has_commit=False, has_poly=False, has_oracle=True):
    oracle_sum_items, poly_sum_items, commit_sum_items = [], [], []
    latex_items, rust_items, poly_sum_rust_items, commit_sum_rust_items = [], [], [], []
    one, rust_const = None, None
    for key, coeff_builder in self.coeff_builders.items():
      latex_items.append(coeff_builder.latex_builder)
      rust_items.append(coeff_builder.rust_builder)
      if key == "one":
        one = latex(coeff_builder.coeff)
        rust_const = rust(coeff_builder.coeff)
      else:
        if has_oracle:
          oracle_sum_items.append(
            "%s\\cdot [%s]" % (
              latex(coeff_builder.coeff),
              coeff_builder.poly.dumps()
            )
          )
        if has_commit:
          commit_sum_items.append(
            "%s\\cdot %s" % (
              latex(coeff_builder.coeff),
              coeff_builder.poly.to_comm()
            )
          )
          commit_sum_rust_items.append("(%s.0).mul(%s.into_repr())" % (
            rust_vk(coeff_builder.poly.to_comm()),
            rust(coeff_builder.coeff)
          ))
        if has_poly:
          poly_sum_items.append("%s\\cdot %s" % (
            latex(coeff_builder.coeff),
            coeff_builder.poly.dumps()
          ))
          poly_sum_rust_items.append("(%s) * (%s)" % (
            rust(coeff_builder.coeff),
            coeff_builder.poly.dumpr_at_index(sym_i - coeff_builder.shifts)
          ))

    if one is not None:
      if has_oracle:
        oracle_sum_items.append("%s" % one)
      if has_poly:
        poly_sum_items.append("%s" % one)
      if has_commit:
        commit_sum_items.append("%s\\cdot \\mathsf{com}(1)" % one)
        commit_sum_rust_items.append(rust_commit_scalar(rust_const))

    if has_oracle:
      latex_items.append(Math("[%s]" % self.poly.dumps()).assign("+".join(oracle_sum_items)))

    if has_poly:
      latex_items.append(Math("%s" % self.poly.dumps()).assign("+".join(poly_sum_items)))
      rust_builder = rust_builder_define_vec_mut(self.poly.to_vec(),
        rust_expression_vector_i(
          rust_sum(poly_sum_rust_items),
          self.length
        )).end()
      if rust_const is not None:
        rust_builder.append(self.poly.to_vec()) \
                    .append("[0]").plus_assign(rust_const).end()

      rust_items.append(rust_builder.append(rust_define(
        self.poly, rust_poly_from_vec(self.poly.to_vec())
      )).end())

    if has_commit:
      latex_items.append(Math("%s" % self.poly.to_comm()).assign("+".join(commit_sum_items)))
      rust_items.append(RustBuilder().let(self.poly.to_comm())
                       .assign_func("Commitment::<E>")
                       .append_to_last(
                         RustBuilder(rust_sum(commit_sum_rust_items))
                         .invoke_method("into_affine")
                       ).end())

    return latex_items, rust_items


class PIOPExecution(PublicCoinProtocolExecution):
  def __init__(self, *args):
    super(PIOPExecution, self).__init__()
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

  def preprocess_polynomial(self, polynomial, degree):
    polynomial._is_preprocessed = True
    if self.indexer_polynomials is not None:
      self.indexer_polynomials.add_polynomial(polynomial, degree)
    else:
      self.indexer_polynomials = IndexerSendPolynomials(polynomial, degree)

  def prover_send_polynomial(self, polynomial, degree):
    if len(self.interactions) > 0 and \
      isinstance(self.interactions[-1], ProverSendPolynomials):
      self.interactions[-1].add_polynomial(polynomial, degree)
    else:
      self.interactions.append(ProverSendPolynomials(polynomial, degree))

    self.prover_polynomials.append(ProverSendPolynomials(polynomial, degree))

  def eval_query(self, name, point, poly):
    self.eval_queries.append(EvalQuery(name, point, poly))
    self.distinct_points.add(tex(point))

  def combine_polynomial(self, poly, coeff_latex_builders, length):
    self.poly_combines.append(CombinePolynomial(poly, coeff_latex_builders, length))

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
      self.preprocess(
        LaTeXBuilder(),
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
    for vc in self.verifier_computations:
      ret.append(vc.dumps())
    for polycom in self.poly_combines:
      for item, rust_items in polycom.dump_items():
        ret.append(VerifierComputes(item, RustBuilder()).dumps())
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
    for vector, size in voexec.indexer_vectors.vectors:
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
    voexec.vec_to_poly_dict = vec_to_poly_dict

  def execute(self, piopexec, *args):
    voexec = piopexec.reference_to_voexec
    n = self.vector_size
    vec_to_poly_dict = voexec.vec_to_poly_dict
    q = Integer(1)
    Ftoq = UnevaluatedExpr(F ** q)

    samples = Samples()
    piopexec.prover_computes_rust(RustBuilder(samples))

    self.debug("Executing VO protocol")
    self.vo.execute(voexec, *args)
    piopexec.prover_inputs = voexec.prover_inputs
    piopexec.verifier_inputs = voexec.verifier_inputs
    piopexec.verifier_computations = voexec.verifier_computations
    piopexec.prover_preparations = voexec.prover_preparations
    piopexec.verifier_preparations = voexec.verifier_preparations

    self.debug("Process interactions")
    for interaction in voexec.interactions:
      if isinstance(interaction, ProverComputes):
        piopexec.prover_computes(interaction.latex_builder, interaction.rust_builder)
      elif isinstance(interaction, VerifierSendRandomnesses):
        piopexec.verifier_send_randomness(*interaction.names)
      elif isinstance(interaction, ProverSubmitVectors):
        for v, size in interaction.vectors:
          randomizer = get_named_vector("delta")
          samples.append(randomizer)
          poly = v.to_named_vector_poly()
          piopexec.prover_computes(
              Math(randomizer).sample(Ftoq).comma(Math(v)).assign(v).double_bar(randomizer),
              RustBuilder().let(v).assign(RustMacro("zero_pad_and_concat").append(
                [v, n, randomizer]
                )).end())
          piopexec.prover_send_polynomial(poly, self.vector_size + q)
          piopexec.prover_computes(
              LaTeXBuilder(),
              RustBuilder().let(poly).assign(
                rust_poly_from_vec(v)
              ).end())
          vec_to_poly_dict[v.key()] = poly

          piopexec.prover_debug(
            "vector %s of length {} = \\n[{}]" % rust(v), "%s.len()" % rust(v),
            rust_fmt_ff_vector(v),
          )
      else:
        raise ValueError("Interaction of type %s should not appear" % type(interaction))

    self.debug("Prepare extended hadamard")
    alpha = Symbol(get_name('alpha'))
    extended_hadamard = []
    shifts = []
    if self.debug_mode:
      check_individual_hadmard = RustBuilder()
    # Some hadamard checks are guaranteed to be zero
    # if the prover is honest. In that case, there is no
    # need for the honest prover to include those terms
    # in t
    ignore_in_t = set()
    for i, had in enumerate(voexec.hadamards):
      alpha_power = alpha ** i
      extended_hadamard.append(alpha_power * had.left_side)
      if not had.one_sided:
        extended_hadamard.append((-alpha_power) * had.right_side)

      if self.debug_mode:
        if had.one_sided:
          side = extended_hadamard[-1]
          check_individual_hadmard.append(rust_check_vector_eq(
              rust_expression_vector_i(
                "(%s) * (%s)" % (
                  (side.a * (1/alpha_power)).dumpr_at_index(sym_i),
                  side.b.dumpr_at_index(sym_i)),
                rust(n)),
              rust_vec_size(rust_zero, n),
              "The %d\'th hadamard check is not satisfied" % (i+1)
              )).end()
        else:
          side1 = extended_hadamard[-1]
          side2 = extended_hadamard[-2]
          check_individual_hadmard.append(rust_check_vector_eq(
              rust_expression_vector_i(
                "(%s) * (%s)" % (
                  (side1.a * (1/alpha_power)).dumpr_at_index(sym_i),
                  side1.b.dumpr_at_index(sym_i)),
                rust(n)),
              rust_expression_vector_i(
                "-(%s) * (%s)" % (
                  (side2.a * (1/alpha_power)).dumpr_at_index(sym_i),
                  side2.b.dumpr_at_index(sym_i)),
                rust(n)),
              "The %d\'th hadamard check is not satisfied" % (i+1)
              )).end()

      else: # One sided, and one of the operand is only a structured vector
        if (not isinstance(had.left_side.a, NamedVector) and \
           not isinstance(had.left_side.a, VectorCombination)) or \
           (not isinstance(had.left_side.b, NamedVector) and \
           not isinstance(had.left_side.b, VectorCombination)):
          ignore_in_t.add(len(extended_hadamard) - 1)
      shifts += had.shifts()

    self.debug("Process inner products")
    if len(voexec.inner_products) > 0:
      beta = Symbol(get_name("beta"))
      piopexec.verifier_send_randomness(beta)
      r = get_named_vector("r")

      rcomputes = LaTeXBuilder().start_math().append(r).assign().end_math() \
                                .space("the sum of:").eol()
      expression_vector = RustMacro("expression_vector", sym_i)
      rcomputes_rust = rust_builder_define_vec(r, expression_vector)
      linear_combination = RustMacro("power_linear_combination", beta)
      r_items = Itemize()
      for i, inner in enumerate(voexec.inner_products):
        difference = inner.dump_hadamard_difference()
        linear_combination.append(inner.dumpr_at_index(sym_i))
        beta_power = beta ** i
        if not inner.one_sided or difference.startswith("-"):
          difference = "\\left(%s\\right)" % difference

        if i > 0:
          difference = "%s\\cdot %s" % (latex(beta_power), difference)

        difference = "$%s$" % difference
        r_items.append(difference)

        alpha_power = alpha ** len(voexec.hadamards)
        extended_hadamard.append((alpha_power * beta_power) * inner.left_side)
        if not inner.one_sided:
          extended_hadamard.append((- alpha_power * beta_power) * inner.right_side)
        shifts += inner.shifts()
      rcomputes.append(r_items)

      expression_vector.append([linear_combination, n])
      piopexec.prover_computes(rcomputes, rcomputes_rust.end())

      randomizer = get_named_vector("delta")
      samples.append(randomizer)
      rtilde = get_named_vector("r", modifier="tilde")
      fr = rtilde.to_named_vector_poly()
      piopexec.prover_computes(Math(randomizer).sample(Ftoq)
        .comma(rtilde).assign(AccumulationVector(r.slice("j"), n))
        .double_bar(randomizer),
        rust_builder_define_vec(
          rtilde,
          rust_vector_concat(
            RustMacro("accumulate_vector", r, "+"),
            randomizer
          )
        ).end()
        .let(fr).assign(rust_poly_from_vec(rtilde)).end())

      piopexec.prover_send_polynomial(fr, n + q)
      vec_to_poly_dict[rtilde.key()] = fr

      extended_hadamard.append((- alpha_power) *
                               VOQuerySide(rtilde - rtilde.shift(1),
                                           PowerVector(1, n)))

      extended_hadamard.append((alpha_power * alpha) *
                               VOQuerySide(rtilde, UnitVector(n)))

      # This last hadamard check involves only a named vector times
      # a unit vector, it does not contribuets to t
      ignore_in_t.add(len(extended_hadamard) - 1)

    self.debug("Process vector t")
    t = get_named_vector("t")
    max_shift = voexec.simplify_max(Max(*shifts))
    piopexec.verifier_send_randomness(alpha)
    
    if self.debug_mode:
      piopexec.prover_computes_rust(check_individual_hadmard)

    tcomputes = LaTeXBuilder().start_math().append(t).assign().end_math() \
                              .space("the sum of:").eol()
    expression_vector = RustMacro("expression_vector", sym_i)
    tcomputes_rust = rust_builder_define_vec(t, expression_vector)
    compute_sum = rust_sum()
    t_items = Itemize()
    for i, side in enumerate(extended_hadamard):
      if not i in ignore_in_t:
        compute_sum.append(side.dumpr_at_index(simplify(sym_i + n)))
        t_items.append("$%s$" % side._dumps("circ"))
    expression_vector.append([compute_sum, 2 * q + max_shift])
    tcomputes.append(t_items)
    piopexec.prover_computes(tcomputes, tcomputes_rust.end())

    randomizer = get_named_vector("delta")
    samples.append(randomizer)
    original_t = t
    t = get_named_vector("t")
    piopexec.prover_computes(
        Math(randomizer).sample(Ftoq)
                        .comma(t)
                        .assign(original_t)
                        .double_bar(randomizer),
        rust_builder_define_vec(t,
          rust_vector_concat(randomizer, original_t)
        ).end())

    tx = t.to_named_vector_poly()
    vec_to_poly_dict[t.key()] = tx
    piopexec.prover_send_polynomial(tx, 2 * q + max_shift)
    extended_hadamard.append(VOQuerySide(-PowerVector(1, max_shift + q).shift(n),
                                         t.shift(n - q)))

    self.debug("Process polynomial h")
    omega = Symbol(get_name('omega'))
    piopexec.verifier_send_randomness(omega)

    if self.debug_mode:
      h_omega_sum_check = RustBuilder()
      h_omega_sum = Symbol(get_name('h_osum'))
      h_omega_sum_check.letmut(h_omega_sum).assign(rust_zero).end()

    hx = get_named_polynomial("h")
    hxcomputes = LaTeXBuilder().start_math().append(hx).assign().end_math() \
                               .space("the sum of:").eol()
    hx_items = Itemize()


    hx_vector_combination = NamedVectorPairCombination()

    if self.debug_mode:
      vecsum = get_named_vector("sum")
      piopexec.prover_computes_rust(
          RustBuilder().letmut(vecsum).assign(rust_vec_size(rust_zero, n + max_shift + q)).end())
      hcheck_vec = get_named_vector("hcheck")
      piopexec.prover_computes_rust(
          RustBuilder().letmut(hcheck_vec).assign(
            rust_vec_size(rust_zero, (n + max_shift + q) * 2 - 1)
          ).end())

    for i, side in enumerate(extended_hadamard):
      self.debug("  Extended Hadamard %d" % (i + 1))
      a = VectorCombination._from(side.a)
      b = VectorCombination._from(side.b)
      atimesb = convolution(a, b, omega)
      hx_vector_combination += atimesb

      for key1, vec_value1 in a.items():
        vec1, value1 = vec_value1
        for key2, vec_value2 in b.items():
          vec2, value2 = vec_value2

          for vec in [vec1, vec2]:
            if isinstance(vec, NamedVector) and vec.key() not in vec_to_poly_dict:
              # This is possible because some named vectors
              # might be locally evaluatable, never submitted
              # by the prover or the indexer
              if not vec.local_evaluate:
                raise Exception("Some non-local vector is not in the dict: %s"
                                % vec.dumps())
              vec_to_poly_dict[vec.key()] = vec.to_named_vector_poly()

          if key1 == "one" and key2 == "one":
            hx_items.append("$%s$" % latex(simplify(
              value1.to_poly_expr(omega / X) * value2.to_poly_expr(X)
            )))
          elif key1 == "one" or key2 == "one":
            named = vec1 if key2 == "one" else vec2
            named_var = omega / X if key2 == "one" else X
            hx_items.append("$%s\\cdot %s$" % (
              add_paren_if_add(latex(simplify(value1.to_poly_expr(omega / X) *
                                              value2.to_poly_expr(X)))),
              vec_to_poly_dict[named.key()].dumps_var(named_var)))
          else:
            hx_items.append("$%s\\cdot %s\\cdot %s$" % (
              add_paren_if_add(latex(simplify(value1.to_poly_expr(omega / X) *
                                              value2.to_poly_expr(X)))),
              vec_to_poly_dict[vec1.key()].dumps_var(omega / X),
              vec_to_poly_dict[vec2.key()].dumps_var(X)))

      if self.debug_mode:
        h_omega_sum_check.append(h_omega_sum).plus_assign(
          rust_eval_vector_expression_i(omega,
            "(%s) * (%s)" % (a.dumpr_at_index(sym_i), b.dumpr_at_index(sym_i)),
            rust(n + max_shift + q)
          )
        ).end()
        piopexec.prover_computes_rust(
            rust_builder_add_expression_vector_to_vector_i(vecsum,
               "(%s) * (%s)" % (a.dumpr_at_index(sym_i),
                                b.dumpr_at_index(sym_i))).end())

        atimesb_vec_naive = get_named_vector("abnaive")
        piopexec.prover_computes_rust(
            RustBuilder().let(atimesb_vec_naive).assign(
              RustMacro("vector_poly_mul",
                  rust_expression_vector_i(
                    a.dumpr_at_index(sym_i),
                    rust(n + max_shift + q),
                  ),
                  rust_expression_vector_i(
                    b.dumpr_at_index(sym_i),
                    rust(n + max_shift + q),
                  ),
                  omega
                )).end())
        piopexec.prover_computes_rust(
          rust_builder_add_vector_to_vector(hcheck_vec, atimesb_vec_naive)
        .end())

        atimesb_computes_rust, atimesb_vector_combination = \
            atimesb.generate_vector_combination(omega)
        piopexec.prover_computes_rust(atimesb_computes_rust)
        atimesb_vec = get_named_vector("atimesb")
        piopexec.prover_computes_rust("// The vector pair here is %s and %s\n" %
            (a.dumps(), b.dumps()))
        piopexec.prover_computes_rust(
          RustBuilder().let(atimesb_vec).assign(rust_expression_vector_i(
              atimesb_vector_combination.dumpr_at_index(sym_i - (n + max_shift + q) + 1),
              2 * (n + max_shift + q) - 1
            )).end()
        )
        piopexec.prover_computes_rust(
          rust_builder_check_vector_eq(
            atimesb_vec,
            RustMacro("zero_pad", atimesb_vec_naive, 2 * (n + max_shift + q) - 1),
            "The %d'th convolution is incorrect" % (i+1)
          ).end()
        )

    if self.debug_mode:
      h_omega_sum_check.append(rust_assert_eq(h_omega_sum, rust_zero)).end()
      piopexec.prover_computes_rust(h_omega_sum_check)
      piopexec.prover_computes_rust(
          rust_builder_check_vector_eq(
            vecsum,
            rust_vec_size(rust_zero, n + max_shift + q),
            "sum of hadamards not zero"
            ).end())

    hxcomputes.append(hx_items)
    h = get_named_vector("h")
    hxcomputes_rust, h_vec_combination = hx_vector_combination.generate_vector_combination(omega)
    piopexec.prover_computes(hxcomputes, hxcomputes_rust)

    self.debug("Compute h1 and h2")

    h_degree, h_inverse_degree = n + max_shift + q, n + max_shift + q
    h1 = get_named_vector("h")
    h2 = get_named_vector("h")
    h1computes_rust = RustBuilder().let(h1).assign(
        rust_expression_vector_i(
           h_vec_combination.dumpr_at_index(sym_i - h_inverse_degree + 1),
           h_inverse_degree - 1)).end()
    h2computes_rust = RustBuilder().let(h2).assign(
        rust_expression_vector_i(
           h_vec_combination.dumpr_at_index(sym_i + 1),
           h_degree - 1)).end()


    # For producing the latex code only
    h1x = get_named_polynomial("h")
    h2x = get_named_polynomial("h")

    piopexec.prover_computes(Math(h1x).assign(hx)
                             .dot(X ** self.degree_bound)
                             .append("\\bmod").append(X ** self.degree_bound),
                             h1computes_rust)
    piopexec.prover_computes(Math(h2x)
                             .assign("\\frac{%s}{X}" % hx.dumps_var(X))
                             .minus("X^{%s}\\cdot %s" %
                                    (latex(-self.degree_bound-1),
                                     h1x.dumps_var(X))),
                             h2computes_rust)

    if self.debug_mode:
      piopexec.prover_computes_rust(
          RustBuilder().let(h).assign(rust_expression_vector_i(
              h_vec_combination.dumpr_at_index(sym_i - h_inverse_degree + 1),
              h_degree + h_inverse_degree - 1
            )).end()
          .append(rust_check_vector_eq(
              h,
              hcheck_vec,
              "h is not expected")).end()
          .append(rust_check_vector_eq(
              h,
              rust_vector_concat(h1, rust_vec(rust_zero), h2),
              "h != h1 || 0 || h2")).end())

      piopexec.prover_computes_rust(
        rust_builder_assert_eq(h_vec_combination.dumpr_at_index(1), rust_zero).end()
      )

    # For the rust code, use the vector instead
    h1x = h1.to_named_vector_poly()
    h2x = h2.to_named_vector_poly()
    piopexec.prover_send_polynomial(h1x, self.degree_bound)
    piopexec.prover_send_polynomial(h2x, h_degree - 1)

    self.debug("Verifier's turn")
    z = Symbol(get_name("z"))
    piopexec.verifier_send_randomness(z)

    self.debug("Collect named polynomials on left")
    left_named_vectors = {}
    for had in extended_hadamard:
      if isinstance(had.a, NamedVector):
        left_named_vectors[had.a.key()] = had.a
      elif isinstance(had.a, VectorCombination):
        for key, vec_value in had.a.items():
          if key != "one" and key not in left_named_vectors:
            vec, value = vec_value
            left_named_vectors[key] = vec

    self.debug("Make evaluation queries")
    query_results = {}
    for key, vec in left_named_vectors.items():
      y = Symbol(get_name("y"))
      if not vec.local_evaluate:
        piopexec.eval_query(y, omega/z, vec_to_poly_dict[key])
        piopexec.prover_computes(
          LaTeXBuilder(),
          RustBuilder().let(y).assign(rust_eval_vector_expression_i(
              omega/z,
              vec.dumpr_at_index(sym_i),
              n + q
            )
          ).end()
        )
      else:
        piopexec.verifier_computes(
            Math(y).assign(vec_to_poly_dict[key].dumps_var(omega/z)),
            RustBuilder.let(y).assign(vec.hint_computation(omega/z))
        )
      query_results[key] = y

    self.debug("Compute gx")
    gx = get_named_polynomial("g")
    coeff_builders = {} # map: key -> (poly, Symbol(coeff), latex_builder, rust_builder)

    if self.debug_mode:
      naive_g = get_named_vector("naive_g")
      piopexec.prover_computes_rust(rust_builder_define_vec_mut(naive_g,
        rust_vec_size(rust_zero, n + max_shift + q)
      ).end())

    # 1. The part contributed by the extended hadamard query
    for i, side in enumerate(extended_hadamard):
      self.debug("  Extended Hadamard %d" % (i + 1))
      """
      assume side.a = f_i(X), side.b = g_i(X)
      then this query branch contributes a f_i(omega/z) * g_i(X) to the final polynomial g(X)
      to compute f_i(omega/z), split f_i(X) into linear combination of named polynomials
      where the coefficients are structured polynomials, i.e.,
      f_i(omega/z) = s_1(omega/z) p_1(omega/z) + ... + s_k(omega/z) p_k(omega/z) + s_0(omega/z)
      """
      a = VectorCombination._from(side.a)
      a_items = []
      for key, vec_value in a.items():
        vec, value = vec_value
        if key == "one":
          # the constant term is a structured polynomial, directly evaluate it at omega/z
          a_items.append(value.to_poly_expr(omega/z))
        else:
          # directly evaluate the coefficient at omega/z
          # then multiply with p_1(omega/z) which has been obtained by querying
          # and stored under the key of p_1 in a dictionary
          a_items.append(query_results[key] * value.to_poly_expr(omega/z))

      # now multiplier should equal f_i(omega/z). if zero, then ignore this term
      multiplier = simplify(sum(a_items))

      # check that multiplier = f_i(omega/z)
      if self.debug_mode:
        piopexec.prover_computes_rust(
          rust_builder_assert_eq(
            multiplier,
            rust_eval_vector_expression_i(
              omega/z, a.dumpr_at_index(sym_i), n + max_shift + q
            )
          ).end()
        )

      if multiplier == 0:
        continue
      b = VectorCombination._from(side.b) * multiplier

      # The naive way to compute f_i(omega/z) g_i(X), is to directly dump g_i(X)
      # coefficients on [1..n+max_shift+q], multiplied by the multiplier
      if self.debug_mode:
        piopexec.prover_computes_rust(
          rust_builder_add_expression_vector_to_vector_i(naive_g, b.dumpr_at_index(sym_i))
          .end())

      # Now decompose g_i(X), i.e., the right side of this Extended Hadamard query
      # multiply every coefficient by the multiplier f_i(omega/z)
      # then evaluate the coefficient at z
      for key, vec_value in b.items():
        vec, value = vec_value
        value = simplify(value.to_poly_expr(z))
        if value == 0:
          raise Exception("value should not be zero")

        # This term is normal: i.e., either the constant term that is a structured
        # polynomial, or a normal NamedVector multiplied by some coefficient
        if (isinstance(vec, NamedVector) and not vec.local_evaluate) or key == "one":
          _key = key
          poly = "one" if key == "one" else vec_to_poly_dict[vec.key()]
          rust_value = rust(value)
          value = latex(value)
        else: # In case it is locally evaluatable polynomial, this term should be
          # regarded as part of the constant, instead of a polynomial. Let the verifier
          # locally evaluate this polynomial at z
          _key = "one"
          poly = "one"
          rust_value = "(%s) * (%s)" % (rust(value), rust(vec.hint_computation(z)))
          value = "%s\\cdot %s" \
                  % (latex(value), vec_to_poly_dict[vec.key()].dumps_var(z))

        # if this polynomial (or constant) has not been handled before, just set the
        # value as the coefficient for this named polynomial
        # otherwise, add the value to the current coefficient
        if _key not in coeff_builders:
          c = Symbol(get_name("c"))
          # Temporarily use list, because the format depends on whether
          # this list size is > 1
          coeff_builders[_key] = CombinationCoeffBuilder(poly, c, [value], [rust_value])
        else:
          # Get the existing coefficient for this named polynomial
          coeff_builder = coeff_builders[_key]
          if coeff_builder.poly != poly:
            raise Exception("%s != %s" % (coeff_builder.poly.dumps(), poly.dumps()))
          coeff_builder.latex_builder.append(value)
          coeff_builder.rust_builder.append(rust_value)

    # 2. The part contributed by h1(X) and h2(X)
    # h1(X) is committed aligned to the right boundary of the universal parameters
    # so we should additionally multiply a power of z to it when computing g(X)
    c = Symbol(get_name("c"))
    coeff_builders[h1x.key()] = CombinationCoeffBuilder(
        h1x, c,
        [- z ** (-self.degree_bound)],
        [- z ** (-self.degree_bound)],
        self.degree_bound - (h_inverse_degree-1))
    c = Symbol(get_name("c"))
    coeff_builders[h2x.key()] = CombinationCoeffBuilder(h2x, c, [- z], [- z], 0)

    if self.debug_mode:
      piopexec.prover_computes_rust(rust_builder_add_expression_vector_to_vector_i(
        naive_g, "(%s) * (%s)" % (h1.dumpr_at_index(sym_i), rust(-z**(-(h_inverse_degree-1))))
      ).end())
      piopexec.prover_computes_rust(rust_builder_add_expression_vector_to_vector_i(
        naive_g, "(%s) * (%s)" % (h2.dumpr_at_index(sym_i), rust(-z))
      ).end())
      # Pass this variable to the zkSNARK, because g has not been computed, cannot
      # make the comparison here.
      piopexec.naive_g = naive_g

      # Check that h(z) = sum_i f_i(omega/z) g_i(z) z^{n+maxshift+q}
      lc = rust_linear_combination(rust_zero)
      for had in extended_hadamard:
        a = VectorCombination._from(had.a)
        b = VectorCombination._from(had.b)
        lc.append(
          rust_eval_vector_expression_i(
            omega/z, a.dumpr_at_index(sym_i), n + max_shift + q
          )
        )
        lc.append(rust_eval_vector_expression_i(z, b.dumpr_at_index(sym_i), n + max_shift + q))
      piopexec.prover_computes_rust(rust_builder_assert_eq(
        rust_builder_eval_vector_as_poly(h, z).mul(z**(-(h_inverse_degree-1))), lc
      ).end())

    # Transform the lists into latex and rust builders
    for key, coeff_builder in coeff_builders.items():
      if len(coeff_builder.latex_builder) > 1:
        latex_builder = LaTeXBuilder().start_math().append(coeff_builder.coeff).assign() \
                                      .end_math().space("the sum of:")
        sum_macro = rust_sum()
        rust_builder = RustBuilder().let(coeff_builder.coeff).assign(sum_macro).end()
        items = Itemize()
        for item in coeff_builder.latex_builder:
          items.append("$%s$" % item)
        for item in coeff_builder.rust_builder:
          sum_macro.append(item)
        latex_builder.append(items)
      else:
        latex_builder = Math(coeff_builder.coeff).assign(coeff_builder.latex_builder[0])
        rust_builder = RustBuilder().let(coeff_builder.coeff).assign(coeff_builder.rust_builder[0]).end()
      coeff_builder.latex_builder = latex_builder
      coeff_builder.rust_builder = rust_builder

    piopexec.combine_polynomial(gx, coeff_builders, self.degree_bound)

    self.debug("Combine polynomial")
    piopexec.eval_check(0, z, gx)
    piopexec.max_degree = h_degree - 1


class ZKSNARK(object):
  def __init__(self):
    self.indexer_computations = []
    self.prover_computations = []
    self.prover_preparations = []
    self.verifier_computations = []
    self.verifier_preparations = []
    self.vk = []
    self.pk = []
    self.proof = []
    self.debug_mode = False

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
    self.prover_computations.append(ProverComputes(latex_builder, rust_builder, False))

  def prover_computes_latex(self, latex_builder):
    self.prover_computes(latex_builder, RustBuilder())

  def prover_computes_rust(self, rust_builder):
    self.prover_computes(LaTeXBuilder(), rust_builder)

  def prover_prepare(self, latex_builder, rust_builder):
    self.prover_preparations.append(ProverComputes(latex_builder, rust_builder))

  def verifier_computes(self, latex_builder, rust_builder):
    self.verifier_computations.append(VerifierComputes(latex_builder, rust_builder, False))

  def verifier_prepare(self, latex_builder, rust_builder):
    self.verifier_preparations.append(VerifierComputes(latex_builder, rust_builder))

  def dump_indexer(self):
    enum = Enumerate()
    for computation in self.indexer_computations:
      enum.append(computation.dumps())
    itemize = Itemize()
    itemize.append("$\\mathsf{pk}:=(%s)$" % ",".join([tex(v) for v in self.vk]))
    itemize.append("$\\mathsf{vk}:=(%s)$" % ",".join([tex(p) for p in self.pk] + [tex(v) for v in self.vk]))
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
    return "".join([computation.dumpr() for computation in self.prover_preparations] +
        [computation.dumpr() for computation in self.prover_computations])

  def dump_verifier(self):
    enum = Enumerate()
    for computation in self.verifier_computations:
      enum.append(computation.dumps())
    return enum.dumps()

  def dump_proof_init(self):
    return ("\n" + " " * 8).join(["let %s = proof.%s;" % (rust(item), rust(item))
                                  for item in self.proof])

  def dump_verifier_rust(self):
    return self.dump_proof_init() + "".join([computation.dumpr() for computation in self.verifier_preparations] +
          [computation.dumpr() for computation in self.verifier_computations])

  def dump_vk_definition(self):
    return "\n    ".join(["pub %s: %s," % (rust(item), get_rust_type(item)) for item in self.vk])

  def dump_pk_definition(self):
    return "\n    ".join(["pub %s: %s," % (rust(item), get_rust_type(item)) for item in self.pk])

  def dump_proof_definition(self):
    return "\n    ".join(["pub %s: %s," % (rust(item), get_rust_type(item)) for item in self.proof])

  def dump_vk_construction(self):
    return ("\n" + " " * 12).join(["%s: %s," % (rust(item), rust(item)) for item in self.vk])

  def dump_pk_construction(self):
    return ("\n" + " " * 12).join(["%s: %s," % (rust(item), rust(item)) for item in self.pk])

  def dump_proof_construction(self):
    return ("\n" + " " * 12).join(["%s: %s," % (rust(item), rust(item)) for item in self.proof])


class ZKSNARKFromPIOPExecKZG(ZKSNARK):
  def __init__(self, piopexec):
    super(ZKSNARKFromPIOPExecKZG, self).__init__()
    self.debug_mode = piopexec.debug_mode

    transcript = [x for x in piopexec.verifier_inputs]

    for preprocess in piopexec.preprocessings:
      self.preprocess(preprocess.latex_builder, preprocess.rust_builder)

    for poly, degree in piopexec.indexer_polynomials.polynomials:
      self.preprocess(Math(poly.to_comm())
                      .assign("\\mathsf{com}\\left(%s, \\mathsf{srs}\\right)"
                              % poly.dumps()),
                      RustBuilder().let(poly.to_comm())
                      .assign_func("vector_to_commitment::<E>")
                      .append_to_last("&powers_of_g")
                      .append_to_last("&%s" % rust(poly.vector))
                      .append_to_last("(%s) as u64" % rust(degree))
                      .invoke_method("unwrap").end())
      self.preprocess_output_vk(poly.to_comm())
      transcript.append(poly.to_comm())

    for p in piopexec.indexer_output_pk:
      self.preprocess_output_pk(p)

    for v in piopexec.indexer_output_vk:
      self.preprocess_output_vk(v)
      transcript.append(v)

    for computation in piopexec.verifier_preparations:
      self.prover_computes(computation.latex_builder, computation.rust_builder)
      self.verifier_computes(computation.latex_builder, computation.rust_builder)

    for interaction in piopexec.interactions:
      if isinstance(interaction, ProverComputes):
        self.prover_computes(interaction.latex_builder, interaction.rust_builder)
      elif isinstance(interaction, VerifierSendRandomnesses):
        for i, r in enumerate(interaction.names):
          compute_hash = Math(r).assign(
            "\\mathsf{H}_{%d}(%s)"
            % (i+1, ",".join([tex(x) for x in transcript]))
          )
          self.prover_computes(compute_hash,
              RustBuilder().let(r).assign().func("hash_to_field::<E::Fr>")
              .append_to_last(RustBuilder().func("to_bytes!")
                .append_to_last([rust_pk_vk(x) for x in transcript])
                .invoke_method("unwrap")).end())
          self.verifier_computes(compute_hash,
              RustBuilder().let(r).assign().func("hash_to_field::<E::Fr>")
              .append_to_last(RustBuilder().func("to_bytes!")
                .append_to_last([rust_vk(x) for x in transcript])
                .invoke_method("unwrap")).end())
      if isinstance(interaction, ProverSendPolynomials):
        for poly, degree in interaction.polynomials:
          commit_computation = Math(poly.to_comm()).assign(
            "\\mathsf{com}\\left(%s, \\mathsf{srs}\\right)"
            % (poly.dumps())
            )
          commit_rust_computation = RustBuilder().let(poly.to_comm())
          if isinstance(poly, NamedPolynomial):
            commit_rust_computation.assign_func("KZG10::commit").append_to_last(poly).end()
          elif isinstance(poly, NamedVectorPolynomial):
            commit_rust_computation.assign_func("vector_to_commitment::<E>") \
              .append_to_last("&pk.powers") \
              .append_to_last("&%s" % rust(poly.vector)) \
              .append_to_last("(%s) as u64" % rust(degree)) \
              .invoke_method("unwrap").end()
          else:
            raise Exception("Unrecognized polynomial type: %s" % type(poly))
          self.prover_computes(commit_computation, commit_rust_computation)
          transcript.append(poly.to_comm())
          self.proof.append(poly.to_comm())

    self.prover_computes(Math(",".join(["%s:=%s" %
      (tex(query.name), tex(query.poly.dumps_var(query.point)))
      for query in piopexec.eval_queries])),
      RustBuilder())
    self.proof += [query.name for query in piopexec.eval_queries]

    for computation in piopexec.verifier_computations:
      self.prover_computes(computation.latex_builder, computation.rust_builder)
      self.verifier_computes(computation.latex_builder, computation.rust_builder)

    for poly_combine in piopexec.poly_combines:
      prover_items, prover_rust_items = poly_combine.dump_items(
          has_oracle=False, has_commit=True, has_poly=True)
      verifier_items, verifier_rust_items = poly_combine.dump_items(
          has_oracle=False, has_commit=True, has_poly=False)
      for item, rust_item in zip(prover_items, prover_rust_items):
        self.prover_computes(item, rust_item)
      for item, rust_item in zip(verifier_items, verifier_rust_items):
        self.verifier_computes(item, rust_item)
      transcript.append(poly_combine.poly.to_comm())

      if piopexec.debug_mode:
        self.prover_computes_rust(rust_builder_assert_eq(
          poly_combine.poly.to_comm(),
          RustBuilder().func("vector_to_commitment::<E>")
          .append_to_last("&pk.powers")
          .append_to_last("&%s" % rust(poly_combine.poly.to_vec()))
          .append_to_last("(%s) as u64" % rust(poly_combine.length))
          .invoke_method("unwrap")
        ).end())

    queries = piopexec.eval_queries + piopexec.eval_checks

    if piopexec.debug_mode:
      z = [query.point for query in queries if query.name == 0][0]
      naive_g = piopexec.naive_g
      self.prover_computes_rust(RustBuilder().let(naive_g.to_named_vector_poly()).assign(
        rust_poly_from_vec(naive_g)
      ).end())
      self.prover_computes_rust(rust_builder_check_poly_eval(
                                 naive_g.to_named_vector_poly(),
                                 z,
                                 rust_zero,
                                 "naive g does not evaluate to 0 at z").end())

    points_poly_dict = {}
    for query in queries:
      key = latex(query.point)
      if key not in points_poly_dict:
        points_poly_dict[key] = []
      points_poly_dict[key].append(query)

    open_proof, open_points, query_tuple_lists, ffs, fcomms, fvals = \
        [], [], [], [], [], []
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
          self.prover_computes_rust(rust_builder_check_poly_eval(
                                    query.poly,
                                    queries[0].point,
                                    rust_zero if query.name == 0
                                              else query.name,
                                    "g does not evaluate to 0 at z").end())

      ffs.append([rust(query.poly) for query in queries])
      fcomms.append([rust_vk(query.poly.to_comm()) for query in queries])
      fvals.append([rust_zero if query.name == 0 else query.name
                    for query in queries])

    fs, gs = ffs
    fcomms, gcomms = fcomms
    fvals, gvals = fvals

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
    points = "\\left\\{%s\\right\\}" % (",".join(tex(p) for p in open_points))
    array = "\\begin{array}{l}\n%s\\\\\n%s\n\\end{array}" % (lists, points)
    open_computation.paren(array)

    open_computation_rust = RustBuilder()
    open_computation_rust.let("fs").assign(rust_vec(fs)).end()
    open_computation_rust.let("gs").assign(rust_vec(gs)).end()
    open_computation_rust.let("z1").assign(open_points[0]).end()
    open_computation_rust.let("z2").assign(open_points[1]).end()

    open_computation_rust.let("rand_xi").assign().func("hash_to_field::<E::Fr>") \
      .append_to_last(RustBuilder().func("to_bytes!") \
        .append_to_last([rust_pk_vk(x) for x in transcript])
        .invoke_method("unwrap")).end()
    open_computation_rust.let("rand_xi_2").assign().func("hash_to_field::<E::Fr>") \
      .append_to_last(RustBuilder().func("to_bytes!") \
        .append_to_last([rust_pk_vk(x) for x in transcript])
        .invoke_method("unwrap")).end()

    lists = "\\\\\n".join([("\\left\\{%s\\right\\}," % (
                            ",".join([("\\left(%s,%s\\right)" %
                                       (tex(query[0]), tex(query[1])))
                                      for query in tuple_list])
                            )) for tuple_list in query_tuple_lists])
    array = "\\begin{array}{l}\n%s\\\\\n%s\n\\left\\{%s\\right\\},[x]_2\\end{array}" \
            % (lists, points, proof_str)
    verify_computation = Math("\\mathsf{vrfy}").paren(array).equals(1)
    verify_computation_rust = RustBuilder()

    verify_computation_rust.let("rand_xi").assign().func("hash_to_field::<E::Fr>") \
      .append_to_last(RustBuilder().func("to_bytes!") \
        .append_to_last([rust_vk(x) for x in transcript])
        .invoke_method("unwrap")).end()
    verify_computation_rust.let("rand_xi_2").assign().func("hash_to_field::<E::Fr>") \
      .append_to_last(RustBuilder().func("to_bytes!") \
        .append_to_last([rust_vk(x) for x in transcript])
        .invoke_method("unwrap")).end()
    verify_computation_rust.let("z1").assign(open_points[0]).end()
    verify_computation_rust.let("z2").assign(open_points[1]).end()
    verify_computation_rust.let("f_commitments").assign(rust_vec(fcomms)).end()
    verify_computation_rust.let("g_commitments").assign(rust_vec(gcomms)).end()
    verify_computation_rust.let("f_values").assign(rust_vec(fvals)).end()
    verify_computation_rust.let("g_values").assign(rust_vec(gvals)).end()

    self.prover_computes(open_computation, open_computation_rust)
    self.verifier_computes(verify_computation, verify_computation_rust)

