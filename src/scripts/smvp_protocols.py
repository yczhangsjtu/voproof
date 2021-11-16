from sympy import Symbol, latex, sympify, Integer, simplify
from sympy.abc import alpha, beta, gamma
from optimized_compiler import VOProtocol
from vector_symbol import get_named_vector, PowerVector, UnitVector, \
                          reset_name_counters, get_name, Matrix, \
                          rust_pk, rust_vk
from latex_builder import Math, AccumulationVector, ExpressionVector, \
                          LaTeXBuilder, ProductAccumulationDivideVector, \
                          add_paren_if_not_atom, tex
from rust_builder import *
                         

class SparseMVP(VOProtocol):
  def __init__(self):
    super(SparseMVP, self).__init__("SparseMVP")

  def preprocess(self, voexec, H, K, ell):
    n = voexec.vector_size
    u = get_named_vector("u")
    w = get_named_vector("w")
    v = get_named_vector("v")
    y = get_named_vector("y")
    voexec.preprocess_rust(rust_builder_define_generator().end())
    voexec.preprocess_latex(Math(u).assign(ExpressionVector("\\gamma^{\\mathsf{row}_i}", ell))),
    voexec.preprocess_latex(Math(w).assign(ExpressionVector("\\gamma^{\\mathsf{col}_i}", ell))),
    voexec.preprocess_latex(Math(v).assign(ExpressionVector("\\mathsf{val}_i", ell))),
    voexec.preprocess_rust(rust_builder_define_matrix_vectors(u, w, v, voexec.M, "gamma").end())
    voexec.preprocess(
      Math(y).assign(u).circ(w),
      rust_builder_define_hadamard_vector(y, u, w).end())

    voexec.preprocess_vector(u, ell)
    voexec.preprocess_vector(w, ell)
    voexec.preprocess_vector(v, ell)
    voexec.preprocess_vector(y, ell)
    voexec.preprocess_output_pk(u)
    voexec.preprocess_output_pk(w)
    voexec.preprocess_output_pk(v)
    voexec.preprocess_output_pk(y)
    u._is_preprocessed = True
    voexec.u = u
    w._is_preprocessed = True
    voexec.w = w
    v._is_preprocessed = True
    voexec.v = v
    y._is_preprocessed = True
    voexec.y = y
    voexec.H = H
    voexec.K = K
    voexec.ell = ell
    return voexec

  def execute(self, voexec, a):
    n, H, K, ell = voexec.vector_size, voexec.H, voexec.K, voexec.ell
    M = voexec.M

    mu = Symbol(get_name("mu"))
    voexec.verifier_computes_rust(rust_builder_define_generator().end())
    voexec.verifier_send_randomness(mu)
    r = get_named_vector("r")
    voexec.prover_computes(Math(r).assign(
      ExpressionVector("\\frac{1}{%s-\\gamma^i}" % tex(mu), H)
    ), RustBuilder().letmut(r).assign(
        RustMacro("expression_vector").append([
            Symbol("i"),
            "(%s) - (%s)" % (rust(mu), PowerVector(gamma, H).dumpr_at_index(Symbol("i"))),
            H]),
      ).end()
      .func("batch_inversion").append_to_last("&mut %s" % rust(r)).end())
    c = get_named_vector("c")
    voexec.prover_computes(Math(c).assign()
                           .transpose(r, paren=False).append("\\boldsymbol{M}"),
                           rust_builder_define_left_sparse_mvp_vector(c, rust_pk(M), r, H, K).end())
    s = get_named_vector("s")
    voexec.prover_computes(Math(s).assign(r).double_bar().paren(-c),
        RustBuilder().let(s).assign(r).invoke_method("iter")
        .invoke_method("map").append_to_last("|a| *a")
        .invoke_method("chain").append_to_last(
          RustBuilder(c).invoke_method("iter").invoke_method("map")
          .append_to_last("|a| -*a")
          ).invoke_method("collect::<Vec<E::Fr>>").end())
    voexec.prover_submit_vector(s, H + K)
    voexec.hadamard_query(
      mu * PowerVector(1, H) - PowerVector(gamma, H),
      s,
      PowerVector(1, H),
      PowerVector(1, H),
    )
    voexec.inner_product_query(
      a.shift(n - H - K),
      s.shift(n - H - K),
    )

    nu = Symbol(get_name("nu"))
    voexec.verifier_send_randomness(nu)

    h = get_named_vector("h")
    rnu = get_named_vector("rnu")
    voexec.prover_computes(LaTeXBuilder(), RustBuilder().letmut(rnu).assign(
        RustMacro("expression_vector").append([
            Symbol("i"),
            "(%s) - (%s)" % (rust(nu), PowerVector(gamma, K).dumpr_at_index(Symbol("i"))),
            K]),
      ).end()
      .func("batch_inversion").append_to_last("&mut %s" % rust(rnu)).end())
    voexec.prover_computes(Math(h).assign(
      ExpressionVector("\\frac{1}{%s-\\gamma^i}" % tex(nu), K)
    ).double_bar(
      ExpressionVector("\\frac{1}{(%s-%s)(%s-%s)}" %
                       (tex(mu), voexec.u.slice(Symbol("i")).dumps(),
                        tex(nu), voexec.w.slice(Symbol("i")).dumps()), ell)
    ), RustBuilder().let(h).assign(rnu).invoke_method("iter")
                    .invoke_method("map").append_to_last("|a| *a")
                    .invoke_method("chain").append_to_last(
                      RustBuilder(rust_pk(voexec.u)).invoke_method("iter")
                      .invoke_method("map").append_to_last("|a| *a")
                      .invoke_method("zip").append_to_last(
                        RustBuilder(rust_pk(voexec.w)).invoke_method("iter")
                        .invoke_method("map").append_to_last("|a| *a")
                      )
                      .invoke_method("map")
                      .append_to_last("|(u, w)| ((%s - u) * (%s - w)).inverse().unwrap()" % (rust(mu), rust(nu))))
                    .invoke_method("collect::<Vec<E::Fr>>").end())
    voexec.prover_submit_vector(h, ell + K)

    voexec.hadamard_query(
      nu * PowerVector(1, K) - PowerVector(gamma, K),
      h,
      PowerVector(1, K),
      PowerVector(1, K),
    )

    voexec.hadamard_query(
      h,
      (mu * nu * PowerVector(1, ell) - mu * voexec.w -
       nu * voexec.u + voexec.y).shift(K),
      PowerVector(1, ell).shift(K),
      PowerVector(1, ell).shift(K),
    )

    voexec.inner_product_query(
      - h.shift(n - K),
      s.shift(n - H - K),
      h.shift(n - ell - K),
      voexec.v.shift(n - ell),
    )


class SparseMVPProverEfficient(VOProtocol):
  def __init__(self):
    super(SparseMVPProverEfficient, self).__init__("SparseMVPProverEfficient")

  def preprocess(self, voexec, H, K, ell):
    n = voexec.vector_size
    u = get_named_vector("u")
    w = get_named_vector("w")
    v = get_named_vector("v")
    y = get_named_vector("y")
    voexec.preprocess(Math(u).assign(
      ExpressionVector("\\gamma^{\\mathsf{row}_i}", ell)
    ), RustBuilder())
    voexec.preprocess(Math(w).assign(
      ExpressionVector("\\gamma^{\\mathsf{col}_i}", ell)
    ), RustBuilder())
    voexec.preprocess(Math(v).assign(
      ExpressionVector("\\mathsf{val}_i", ell)
    ), RustBuilder())
    voexec.preprocess(Math(y).assign(u).circ(w), RustBuilder())
    voexec.preprocess_vector(u, ell)
    voexec.preprocess_vector(w, ell)
    voexec.preprocess_vector(v, ell)
    voexec.preprocess_vector(y, ell)
    voexec.preprocess_output_pk(u)
    voexec.preprocess_output_pk(w)
    voexec.preprocess_output_pk(v)
    voexec.preprocess_output_pk(y)
    voexec.u = u
    voexec.w = w
    voexec.v = v
    voexec.y = y
    voexec.H = H
    voexec.K = K
    voexec.ell = ell
    return voexec

  def execute(self, voexec, a, b):
    n, H, K, ell = voexec.vector_size, voexec.H, voexec.K, voexec.ell

    mu = Symbol(get_name("mu"))
    voexec.verifier_send_randomness(mu)
    r = get_named_vector("r")
    voexec.prover_computes(Math(r).assign(
      ExpressionVector("\\frac{1}{\\alpha-\\gamma^i}", H)
    ), RustBuilder())
    voexec.prover_submit_vector(r, H)
    voexec.hadamard_query(
      mu * PowerVector(1, H) - PowerVector(gamma, H),
      r,
      PowerVector(1, H),
      PowerVector(1, H),
    )
    c = get_named_vector("c")
    voexec.prover_computes(Math(c).assign()
                           .transpose(r, paren=False).append("\\boldsymbol{M}"),
                           RustBuilder())
    voexec.prover_submit_vector(c, K)
    voexec.inner_product_query(
      a.shift(n - K),
      c.shift(n - K),
      b.shift(n - H),
      r.shift(n - H),
    )

    nu = Symbol(get_name("nu"))
    voexec.verifier_send_randomness(nu)

    r = get_named_vector("r")
    voexec.prover_computes(Math(r).assign(
      ExpressionVector("\\frac{1}{\\beta-\\gamma^i}", K)),
      RustBuilder())
    voexec.prover_submit_vector(r, K)

    t = get_named_vector("t")
    voexec.prover_computes(Math(t).assign(
      ExpressionVector("\\frac{1}{(\\alpha-%s)(\\beta-%s}" %
                       (voexec.u.slice(Symbol("i")).dumps(),
                        voexec.w.slice(Symbol("i")).dumps()), ell)),
      RustBuilder())
    voexec.prover_submit_vector(t, ell)

    voexec.hadamard_query(
      nu * PowerVector(1, K) - PowerVector(gamma, K),
      r,
      PowerVector(1, K),
      PowerVector(1, K),
    )

    voexec.hadamard_query(
      t,
      mu * nu * PowerVector(1, K) - mu * voexec.w -
      nu * voexec.u + voexec.y,
      PowerVector(1, K),
      PowerVector(1, K),
    )

    voexec.inner_product_query(
      t.shift(n - ell),
      voexec.v.shift(n - ell),
      c.shift(n - K),
      r.shift(n - K),
    )


class R1CS(VOProtocol):
  def __init__(self):
    super(R1CS, self).__init__("R1CS")

  def preprocess(self, voexec, H, K, sa, sb, sc):
    M = Matrix("M")
    voexec.preprocess_rust(rust_builder_init_size(H, "nrows").end())
    # voexec.preprocess_rust(rust_builder_init_size(K, "ncols").end())
    voexec.preprocess_rust(rust_builder_init_size(sa, "adensity").end())
    voexec.preprocess_rust(rust_builder_init_size(sb, "bdensity").end())
    voexec.preprocess_rust(rust_builder_init_size(sc, "cdensity").end())

    voexec.preprocess_rust(
      rust_builder_concat_matrix_vertically(M, H,
        "cs.arows", "cs.brows", "cs.crows",
        "cs.acols", "cs.bcols", "cs.ccols",
        "cs.avals", "cs.bvals", "cs.cvals").end())

    voexec.preprocess_output_pk(M)
    voexec.M = M
    M._is_preprocessed = True

    SparseMVP().preprocess(voexec, H * 3, K, sa + sb + sc)
    voexec.r1cs_H = H
    voexec.r1cs_K = K
    voexec.sa = sa
    voexec.sb = sb
    voexec.sc = sc
    return voexec

  def execute(self, voexec, x, w, ell):
    voexec.input_instance(x)
    voexec.input_witness(w)

    H, K, sa, sb, sc, n = voexec.r1cs_H, voexec.r1cs_K, \
                          voexec.sa, voexec.sb, voexec.sc, voexec.vector_size
    M = voexec.M

    voexec.verifier_computes_rust(rust_builder_define_vec(x, "x.instance.clone()").end())
    voexec.prover_computes_rust(rust_builder_define_vec(w, "w.witness.clone()").end())
    voexec.verifier_computes_rust(rust_builder_init_size(H, "nrows").end())
    voexec.verifier_computes_rust(rust_builder_init_size(K, "ncols").end())
    voexec.verifier_computes_rust(rust_builder_init_size(sa, "adensity").end())
    voexec.verifier_computes_rust(rust_builder_init_size(sb, "bdensity").end())
    voexec.verifier_computes_rust(rust_builder_init_size(sc, "cdensity").end())
    voexec.verifier_computes_rust(rust_builder_init_size(ell, "input_size").end())

    u = get_named_vector("u")
    voexec.prover_computes(Math(u).assign().paren(
        LaTeXBuilder("\\boldsymbol{M}").paren(
          LaTeXBuilder(1).double_bar(x).double_bar(w)
        )
      ).double_bar(1).double_bar(x).double_bar(w),
      rust_builder_define_concat_vector(u,
        rust_sparse_mvp_vector(
          rust_pk(M),
          rust_vector_concat(
            rust_vec(rust_one), x, w
          ),
          H * 3, K
        ),
        rust_vec(rust_one), x, w
      ).end())

    voexec.prover_submit_vector(u, 3 * H + K)
    voexec.run_subprotocol(SparseMVP(), u)
    voexec.hadamard_query(
      u.shift(n-H),
      u.shift(n-H*2),
      PowerVector(1, H).shift(n-H),
      u.shift(n-H*3),
    )
    voexec.hadamard_query(
      PowerVector(1, ell+1).shift(H*3),
      u - x.shift(H*3+1) - UnitVector(H*3+1),
    )


class R1CSProverEfficient(VOProtocol):
  def __init__(self):
    super(R1CSProverEfficient, self).__init__("R1CS")

  def preprocess(self, voexec, H, K, s):
    SparseMVPProverEfficient().preprocess(voexec, H * 3, K, s)
    voexec.r1cs_H = H
    voexec.r1cs_K = K
    voexec.s = s
    return voexec

  def execute(self, voexec, x, w, ell):
    voexec.input_instance(x)
    voexec.input_witness(w)

    H, K, s, n = voexec.r1cs_H, voexec.r1cs_K, voexec.s, voexec.vector_size
    y = get_named_vector("y")
    voexec.prover_computes(Math(y).assign().paren(
      Math("\\boldsymbol{M}").paren(Math(1).double_bar(x).double_bar(w))
    ),RustBuilder())
    voexec.prover_submit_vector(y, 3 * H)
    voexec.prover_submit_vector(w, H - ell - 1)
    voexec.run_subprotocol(SparseMVPProverEfficient(),
                           UnitVector(1) + x.shift(1) +
                           w.shift(ell + 1), y)
    voexec.hadamard_query(
      y.shift(n-H),
      y.shift(n-H*2),
      PowerVector(1, H).shift(n-H),
      y.shift(n-H*3),
    )


class HPR(VOProtocol):
  def __init__(self):
    super(HPR, self).__init__("HPR")

  def preprocess(self, voexec, H, K, s):
    SparseMVP().preprocess(voexec, H, K * 3 + 1, s)
    voexec.hpr_H = H
    voexec.hpr_K = K
    voexec.s = s
    return voexec

  def execute(self, voexec, x, w1, w2, w3, ell):
    voexec.input_instance(x)
    voexec.input_witness(w1)
    voexec.input_witness(w2)
    voexec.input_witness(w3)

    H, K, s, n = voexec.hpr_H, voexec.hpr_K, voexec.s, voexec.vector_size
    w = get_named_vector("w")
    voexec.prover_computes(Math(w).assign(w1).double_bar(w2).double_bar(w3), RustBuilder())
    voexec.prover_submit_vector(w, 3 * K)
    voexec.run_subprotocol(SparseMVP(),
                           x + w.shift(ell + 1) +
                           UnitVector(ell + 1))
    voexec.hadamard_query(
      w.shift(n-K),
      w.shift(n-K*2),
      PowerVector(1, K).shift(n-K),
      w.shift(n-K*3),
    )


class HPRProverEfficient(VOProtocol):
  def __init__(self):
    super(HPRProverEfficient, self).__init__("HPR")

  def preprocess(self, voexec, H, K, s):
    SparseMVPProverEfficient().preprocess(voexec, H, K * 3 + 1, s)
    voexec.hpr_H = H
    voexec.hpr_K = K
    voexec.s = s
    return voexec

  def execute(self, voexec, x, w1, w2, w3, ell):
    voexec.input_instance(x)
    voexec.input_witness(w1)
    voexec.input_witness(w2)
    voexec.input_witness(w3)

    H, K, s, n = voexec.hpr_H, voexec.hpr_K, voexec.s, voexec.vector_size
    w = get_named_vector("w")
    voexec.prover_computes(Math(w).assign(w1).double_bar(w2).double_bar(w3), RustBuilder())
    voexec.prover_submit_vector(w, 3 * K)
    voexec.run_subprotocol(SparseMVPProverEfficient(),
                           w.shift(1) + UnitVector(1), x)
    voexec.hadamard_query(
      w.shift(n-K),
      w.shift(n-K*2),
      PowerVector(1, K).shift(n-K),
      w.shift(n-K*3),
    )


