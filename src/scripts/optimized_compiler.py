from vector_symbol import NamedVector, PowerVector, UnitVector, \
                   NamedPolynomial, NamedVectorPolynomial, \
                   SparseVector, get_name, reset_name_counters, \
                   StructuredVector, VectorCombination, get_named_vector, \
                   PolynomialCombination, simplify_max_with_hints, \
                   get_named_polynomial
from latex_builder import tex, LaTeXBuilder, AccumulationVector, \
                          ExpressionVector, Math, Enumerate, Itemize, \
                          add_paren_if_add
from sympy import Symbol, Integer, UnevaluatedExpr, Expr, Max, simplify, \
                  latex, srepr, Add, Mul
from sympy.core.numbers import Infinity
from sympy.abc import alpha, beta, gamma, X, D, S
from os.path import basename

F = Symbol("\\mathbb{F}")
Fstar = Symbol("\\mathbb{F}^*")


class Computes(object):
  def __init__(self, latex_builder, owner=None):
    self.latex_builder = latex_builder
    self.owner = owner

  def dumps(self):
    ret = self.latex_builder.dumps()
    if self.owner is not None:
      ret = "\\%s computes %s" % (self.owner, ret)
    return ret


class IndexerComputes(object):
  def __init__(self, latex_builder, has_indexer=True):
    super(IndexerComputes, self).__init__(latex_builder, "indexer"
                                              if has_indexer else None)


class ProverComputes(Computes):
  def __init__(self, latex_builder, has_prover=True):
    super(ProverComputes, self).__init__(latex_builder, "prover"
                                                        if has_prover else None)


class VerifierComputes(Computes):
  def __init__(self, latex_builder, has_verifier=True):
    super(VerifierComputes, self).__init__(latex_builder,
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
    self.interactions = []
    self.verifier_computations = []

  def input_instance(self, arg):
    self.verifier_inputs.append(arg)
    self.prover_inputs.append(arg)

  def input_witness(self, arg):
    self.prover_inputs.append(arg)

  def preprocess(self, latex_builder):
    self.preprocessings.append(latex_builder)

  def preprocess_output_pk(self, expr):
    self.indexer_output_pk.append(expr)

  def preprocess_output_vk(self, expr):
    self.indexer_output_vk.append(expr)

  def prover_computes(self, latex_builder):
    self.interactions.append(ProverComputes(latex_builder))

  def verifier_computes(self, latex_builder):
    self.verifier_computations.append(VerifierComputes(latex_builder))

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
    ret = Enumerate()
    for pp in self.preprocessings:
      ret.append(pp.dumps())
    ret.append(self.indexer_vectors.dumps())
    for interaction in self.interactions:
      ret.append(interaction.dumps())
    for had in self.hadamards:
      ret.append(had.dumps())
    for inner in self.inner_products:
      ret.append(inner.dumps())
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


class CombinePolynomial(object):
  def __init__(self, poly, coeff_latex_builders):
    self.poly = poly
    self.coeff_latex_builders = coeff_latex_builders

  def dump_items(self, has_commit=False, has_poly=False, has_oracle=True):
    oralce_sum_items, poly_sum_items, commit_sum_items, items, one = \
        [], [], [], [], None
    for key, poly_coeff_lb in self.coeff_latex_builders.items():
      # The coeff here must be Symbol
      poly, coeff, latex_builder = poly_coeff_lb
      items.append(latex_builder)
      if key == "one":
        one = latex(coeff)
      else:
        if has_oracle:
          oracle_sum_items.append("%s\\cdot [%s]" % (latex(coeff), poly.dumps()))
        if has_commit:
          commit_sum_items.append("%s\\cdot %s" % (latex(coeff), poly.dump_comm()))
        if has_poly:
          poly_sum_items.append("%s\\cdot %s" % (latex(coeff), poly.dumps()))

    if one is not None:
      if has_oracle:
        oracle_sum_items.append("%s" % one)
      if has_poly:
        poly_sum_items.append("%s" % one)
      if has_commit:
        commit_sum_items.append("%s\\cdot \\mathsf{com}(1)" % one)

    if has_oracle:
      items.append(Math("[%s]" % self.poly.dumps()).assign("+".join(oracle_sum_items)))
    if has_poly:
      items.append(Math("%s" % self.poly.dumps()).assign("+".join(poly_sum_items)))
    if has_commit:
      items.append(Math("%s" % self.poly.dump_comm()).assign("+".join(commit_sum_items)))

    return items


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
    self._symbol_dict = {}
    self._power_poly_dict = {}
    self._auto_vector_dict = {}

  def preprocess_polynomial(self, polynomial, degree):
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

  def combine_polynomial(self, poly, coeff_latex_builders):
    self.poly_combines.append(CombinePolynomial(poly, coeff_latex_builders))

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
      for item in polycom.dump_items():
        ret.append(VerifierComputes(item).dumps())
    for query in self.eval_checks:
      ret.append(query.dumps_check())
    return ret.dumps()



class PIOPFromVOProtocol(object):
  def __init__(self, vo, vector_size, degree_bound):
    self.vo = vo
    self.vector_size = vector_size
    self.degree_bound = degree_bound
    self.debug_mode = False

  def preprocess(self, piopexec, *args):
    voexec = VOProtocolExecution(self.vector_size)
    vec_to_poly_dict = {}
    self.vo.preprocess(voexec, *args)
    for pp in voexec.preprocessings:
      piopexec.preprocess(pp)
    for vector, size in voexec.indexer_vectors.vectors:
      poly = vector.to_named_vector_poly()
      piopexec.preprocess_polynomial(vector.to_named_vector_poly(), size)
      vec_to_poly_dict[vector.key()] = poly
    piopexec.indexer_output_pk = voexec.indexer_output_pk
    piopexec.indexer_output_vk = voexec.indexer_output_vk
    piopexec.reference_to_voexec = voexec
    voexec.vec_to_poly_dict = vec_to_poly_dict

  def debug(self, info):
    if self.debug_mode:
      print(info)

  def execute(self, piopexec, *args):
    voexec = piopexec.reference_to_voexec
    n = self.vector_size
    vec_to_poly_dict = voexec.vec_to_poly_dict
    q = Integer(1)
    Ftoq = UnevaluatedExpr(F ** q)

    self.debug("Executing VO protocol")
    self.vo.execute(voexec, *args)
    self.prover_inputs = voexec.prover_inputs
    self.verifier_inputs = voexec.verifier_inputs
    self.verifier_computations = voexec.verifier_computations

    self.debug("Process interactions")
    for interaction in voexec.interactions:
      if isinstance(interaction, ProverComputes):
        piopexec.prover_computes(interaction.latex_builder)
      elif isinstance(interaction, VerifierSendRandomnesses):
        piopexec.verifier_send_randomness(*interaction.names)
      elif isinstance(interaction, ProverSubmitVectors):
        for v, size in interaction.vectors:
          randomizer = get_named_vector("delta")
          poly = v.get_poly_with_same_name()
          piopexec.prover_computes(Math(randomizer).sample(Ftoq)
            .comma(poly)
            .assign("f_{%s\\|%s}(X)" % (v.dumps(), randomizer.dumps()))
          )
          piopexec.prover_send_polynomial(poly, self.vector_size + q)
          vec_to_poly_dict[v.key()] = poly

    self.debug("Prepare extended hadamard")
    alpha = Symbol(get_name('alpha'))
    extended_hadamard = []
    shifts = []
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
      r_items = Itemize()
      for i, inner in enumerate(voexec.inner_products):
        difference = inner.dump_hadamard_difference()
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

      piopexec.prover_computes(rcomputes)

      randomizer = get_named_vector("delta")
      rtilde = get_named_vector("r", modifier="tilde")
      piopexec.prover_computes(Math(randomizer).sample(Ftoq)
        .comma(rtilde).assign(AccumulationVector(r.slice("j"), n))
        .double_bar(randomizer))
      fr = rtilde.to_named_vector_poly()
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
    tcomputes = LaTeXBuilder().start_math().append(t).assign().end_math() \
                              .space("the sum of:").eol()
    t_items = Itemize()
    for i, side in enumerate(extended_hadamard):
      if not i in ignore_in_t:
        t_items.append("$%s$" % side._dumps("circ"))

    randomizer = get_named_vector("delta")
    tx = get_named_polynomial("t")
    vec_to_poly_dict[t.key()] = tx
    tcomputes.append(t_items)
    piopexec.prover_computes(tcomputes)
    piopexec.prover_computes(Math(randomizer).sample(Ftoq)
      .comma(tx).assign("f_{%s\\|%s}(X)" %
                        (randomizer.dumps(),
                         t.slice(n + 1, Infinity).dumps())))
    piopexec.prover_send_polynomial(tx, 2 * q + max_shift)
    # t should be replaced by delta||t_{[n+1:]}, however, there are no more
    # computations involving vectors, only polynomials, so neglecting this
    # will not affect the generated latex code
    extended_hadamard.append(VOQuerySide(-PowerVector(1, max_shift + q).shift(n),
                                         t.shift(n - q)))

    self.debug("Process polynomial h")
    omega = Symbol(get_name('omega'))
    piopexec.verifier_send_randomness(omega)
    hx = get_named_polynomial("h")
    hxcomputes = LaTeXBuilder().start_math().append(hx).assign().end_math() \
                               .space("the sum of:").eol()
    hx_items = Itemize()

    for i, side in enumerate(extended_hadamard):
      self.debug("  Extended Hadamard %d" % (i + 1))
      a = VectorCombination._from(side.a)
      b = VectorCombination._from(side.b)
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

    hxcomputes.append(hx_items)
    piopexec.prover_computes(hxcomputes)

    self.debug("Compute h1 and h2")
    h_degree, h_inverse_degree = n + max_shift + q, n + max_shift + q
    h1x = get_named_polynomial("h")
    h2x = get_named_polynomial("h")

    piopexec.prover_computes(Math(h1x).assign(hx)
                             .dot(X ** self.degree_bound)
                             .append("\\bmod").append(X ** self.degree_bound))
    piopexec.prover_computes(Math(h2x)
                             .assign("\\frac{%s}{X}" % hx.dumps_var(X))
                             .minus("X^{%s}\\cdot %s" %
                                    (latex(-self.degree_bound-1),
                                     h1x.dumps_var(X))))
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
      else:
        piopexec.verifier_computes(Math(y).assign(vec_to_poly_dict[key].dumps_var(omega/z)))
      query_results[key] = y

    self.debug("Compute gx")
    gx = get_named_polynomial("g")
    coeff_builders = {} # map: key -> (poly, Symbol(coeff), latex_builder)

    # 1. The part contributed by the extended hadamard query
    for i, side in enumerate(extended_hadamard):
      self.debug("  Extended Hadamard %d" % (i + 1))
      a = VectorCombination._from(side.a)
      a_items = []
      for key, vec_value in a.items():
        vec, value = vec_value
        if key == "one":
          a_items.append(value.to_poly_expr(omega/z))
        else:
          a_items.append(query_results[key] * value.to_poly_expr(omega/z))

      multiplier = simplify(sum(a_items))
      if multiplier == 0:
        continue

      b = VectorCombination._from(side.b) * multiplier
      for key, vec_value in b.items():
        vec, value = vec_value
        value = simplify(value.to_poly_expr(z))
        if value == 0:
          raise Exception("value should not be zero")
        if (isinstance(vec, NamedVector) and not vec.local_evaluate) or key == "one":
          _key = key
          poly = "one" if key == "one" else vec_to_poly_dict[vec.key()]
          value = latex(value)
        else: # In case it is locally evaluatable polynomial
          _key = "one"
          poly = "one"
          value = "%s\\cdot %s" \
                  % (latex(value), vec_to_poly_dict[vec.key()].dumps_var(z))

        if _key not in coeff_builders:
          c = Symbol(get_name("c"))
          # Temporarily use list, because the format depends on whether
          # this list size is > 1
          coeff_builders[_key] = (poly, c, [value]) 
        else:
          _poly, c, items = coeff_builders[_key]
          if _poly != poly:
            raise Exception("%s != %s" % (_poly.dumps(), poly.dumps()))
          items.append(value)
    
    # 2. The part contributed by h1(X) and h2(X)
    c = Symbol(get_name("c"))
    coeff_builders[h1x.key()] = (h1x, c, [- z ** self.degree_bound])
    c = Symbol(get_name("c"))
    coeff_builders[h2x.key()] = (h2x, c, [- z])

    # Transform the lists into latex builders
    _coeff_builders = {}
    for key, poly_coeff_lb in coeff_builders.items():
      poly, coeff, coeff_list = poly_coeff_lb
      if len(coeff_list) > 1:
        latex_builder = LaTeXBuilder().start_math().append(coeff).assign() \
                                      .end_math().space("the sum of:")
        items = Itemize()
        for item in coeff_list:
          items.append("$%s$" % item)
        latex_builder.append(items)
      else:
        latex_builder = Math(coeff).assign(coeff_list[0])

      _coeff_builders[key] = (poly, coeff, latex_builder)

    coeff_builders = _coeff_builders

    piopexec.combine_polynomial(gx, coeff_builders)

    self.debug("Combine polynomial")
    piopexec.eval_check(0, z, gx)
    piopexec.max_degree = h_degree - 1


class ZKSNARK(object):
  def __init__(self):
    self.indexer_computations = []
    self.prover_computations = []
    self.verifier_computations = []
    self.vk = []
    self.pk = []
    self.proof = []

  def preprocess(self, computation):
    self.indexer_computations.append(computation)

  def preprocess_output_vk(self, expr):
    self.vk.append(expr)

  def preprocess_output_pk(self, expr):
    self.pk.append(expr)

  def prover_computes(self, latex_builder):
    if isinstance(latex_builder, str):
      raise Exception("latex_builder cannot be str: %s" % latex_builder)
    self.prover_computations.append(ProverComputes(latex_builder, False))

  def verifier_computes(self, latex_builder):
    self.verifier_computations.append(VerifierComputes(latex_builder, False))

  def dump_indexer(self):
    enum = Enumerate()
    for computation in self.indexer_computations:
      enum.append(computation.dumps())
    itemize = Itemize()
    itemize.append("$\\mathsf{pk}:=(%s)$" % ",".join([tex(v) for v in self.vk]))
    itemize.append("$\\mathsf{vk}:=(%s)$" % ",".join([tex(p) for p in self.pk] + [tex(v) for v in self.vk]))
    enum.append("Output\n" + itemize.dumps())
    return enum.dumps()

  def dump_prover(self):
    enum = Enumerate()
    for computation in self.prover_computations:
      enum.append(computation.dumps())
    enum.append("Output $\\pi:=\\left(%s\\right)$" %
                ",".join(tex(p) for p in self.proof))
    return enum.dumps()

  def dump_verifier(self):
    enum = Enumerate()
    for computation in self.verifier_computations:
      enum.append(computation.dumps())
    return enum.dumps()


class ZKSNARKFromPIOPExecKZG(ZKSNARK):
  def __init__(self, piopexec):
    super(ZKSNARKFromPIOPExecKZG, self).__init__()

    transcript = [x for x in piopexec.verifier_inputs]

    for preprocess in piopexec.preprocessings:
      self.preprocess(preprocess)

    for poly, degree in piopexec.indexer_polynomials.polynomials:
      self.preprocess(Math(poly.dump_comm())
                      .assign("\\mathsf{com}\\left(%s, \\mathsf{srs}\\right)"
                              % poly.dumps()))
      self.preprocess_output_vk(poly.dump_comm())
      transcript.append(poly.dump_comm())

    for p in piopexec.indexer_output_pk:
      self.preprocess_output_pk(p)

    for v in piopexec.indexer_output_vk:
      self.preprocess_output_vk(v)
      transcript.append(v)

    for interaction in piopexec.interactions:
      if isinstance(interaction, ProverComputes):
        self.prover_computes(interaction.latex_builder)
      elif isinstance(interaction, VerifierSendRandomnesses):
        for i, r in enumerate(interaction.names):
          compute_hash = Math(r).assign(
            "\\mathsf{H}_{%d}(%s)"
            % (i+1, ",".join([tex(x) for x in transcript]))
          )
          self.prover_computes(compute_hash)
          self.verifier_computes(compute_hash)
      if isinstance(interaction, ProverSendPolynomials):
        for poly, degree in interaction.polynomials:
          self.prover_computes(Math(poly.dump_comm()).assign(
            "\\mathsf{com}\\left(%s, \\mathsf{srs}\\right)"
            % (poly.dumps())
          ))
          transcript.append(poly.dump_comm())
          self.proof.append(poly.dump_comm())

    self.prover_computes(Math(",".join(["%s:=%s" %
      (tex(query.name), tex(query.poly.dumps_var(query.point)))
      for query in piopexec.eval_queries])))
    self.proof += [query.name for query in piopexec.eval_queries]

    for computation in piopexec.verifier_computations:
      self.prover_computes(computation.latex_builder)
      self.verifier_computes(computation.latex_builder)

    for poly_combine in piopexec.poly_combines:
      prover_items = poly_combine.dump_items(has_oracle=False, has_commit=True, has_poly=True)
      verifier_items = poly_combine.dump_items(has_oracle=False, has_commit=True, has_poly=False)
      for item in prover_items:
        self.prover_computes(item)
      for item in verifier_items:
        self.verifier_computes(item)

    queries = piopexec.eval_queries + piopexec.eval_checks
    points_poly_dict = {}
    for query in queries:
      key = latex(query.point)
      if key not in points_poly_dict:
        points_poly_dict[key] = []
      points_poly_dict[key].append(query)

    open_proof, open_points, query_tuple_lists = [], [], []
    for point, queries in points_poly_dict.items():
      open_proof.append(Symbol(get_name("W")))
      open_points.append(queries[0].point)
      query_tuple_lists.append([(query.poly.dump_comm(),
                                 query.name, query.poly.dumps())
                                for query in queries])

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

    lists = "\\\\\n".join([("\\left\\{%s\\right\\}," % (
                            ",".join([("\\left(%s,%s\\right)" %
                                       (tex(query[0]), tex(query[1])))
                                      for query in tuple_list])
                            )) for tuple_list in query_tuple_lists])
    array = "\\begin{array}{l}\n%s\\\\\n%s\n\\left\\{%s\\right\\},[x]_2\\end{array}" \
            % (lists, points, proof_str)
    verify_computation = Math("\\mathsf{vrfy}").paren(array).equals(1)
    self.prover_computes(open_computation)
    self.verifier_computes(verify_computation)

