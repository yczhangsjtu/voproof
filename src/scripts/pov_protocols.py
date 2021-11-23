from sympy import Symbol, latex, sympify, Integer, simplify
from sympy.abc import alpha, beta, gamma  # , X, D, S
from compiler.vo_protocol import VOProtocol
from compiler.symbol.vector import get_named_vector, PowerVector, UnitVector
from compiler.symbol.names import reset_name_counters, get_name
from compiler.builder.latex import Math, AccumulationVector, ExpressionVector, \
    LaTeXBuilder, ProductAccumulationDivideVector, \
    add_paren_if_not_atom, tex
from compiler.builder.rust import *

# ell = Symbol("\\ell", positive=True)
# m = Symbol("m", positive=True)
# n = Symbol("n", positive=True)
# H = Symbol("H", positive=True)
# K = Symbol("K", positive=True)
# s = Symbol("s", positive=True)
#
# Ca = Symbol("C_a", positive=True)
# Cm = Symbol("C_m", positive=True)
# Cc = Symbol("C_c", positive=True)
# k = Symbol("k", positive=True)


class ProductEq(VOProtocol):
  def __init__(self):
    super(ProductEq, self).__init__("ProductEq")

  def execute(self, voexec, u, v, ell):
    named_u = self.get_named_vector_for_latex(u, "u", voexec)
    named_v = self.get_named_vector_for_latex(v, "v", voexec)
    n = voexec.vector_size

    r = get_named_vector("r")
    voexec.prover_computes_latex(Math(r).assign(ProductAccumulationDivideVector(
        named_u, named_v, ell)))

    voexec.prover_submit_vector(r, ell)
    voexec.hadamard_query(
        r.shift(n - ell + 1) + UnitVector(n - ell + 1),
        u.shift(n - ell),
        r.shift(n - ell),
        v.shift(n - ell),
    )
    voexec.hadamard_query(
        r - UnitVector(ell),
        UnitVector(ell),
    )


class TripleProductEq(VOProtocol):
  def __init__(self):
    super(TripleProductEq, self).__init__("ProductEq")

  def execute(self, voexec, u1, u2, u3, v1, v2, v3, ell):
    n = voexec.vector_size

    u = get_named_vector("u")
    voexec.prover_computes_latex(Math(u).assign(add_paren_if_not_atom(u1))
                                  .circ(add_paren_if_not_atom(u2))
                                  .circ(add_paren_if_not_atom(u3)))
    v = get_named_vector("v")
    voexec.prover_computes_latex(Math(v).assign(add_paren_if_not_atom(v1))
                                  .circ(add_paren_if_not_atom(v2))
                                  .circ(add_paren_if_not_atom(v3)))

    r = get_named_vector("r")
    voexec.prover_computes_latex(Math(r).assign(ProductAccumulationDivideVector(
        u, v, ell
    )))

    s = get_named_vector("s")
    voexec.prover_computes_latex(Math(s).assign(r)
                                  .slash(add_paren_if_not_atom(v1))
                                  .circ(add_paren_if_not_atom(u1)))

    t = get_named_vector("s")
    voexec.prover_computes_latex(Math(s).assign()
                           .paren(r.shift(1) + UnitVector(1) - UnitVector(ell + 1))
                           .slash(add_paren_if_not_atom(u2))
                           .circ(add_paren_if_not_atom(v2)))

    voexec.prover_submit_vector(r, ell)
    voexec.prover_submit_vector(s, ell)
    voexec.prover_submit_vector(t, ell)
    voexec.hadamard_query(s, v1, r, u1)
    voexec.hadamard_query(t, u2, r.shift(1) + UnitVector(1), v2)
    voexec.hadamard_query(s, u3, t, v3)
    voexec.hadamard_query(UnitVector(ell), r - UnitVector(ell))


class Permute(VOProtocol):
  def __init__(self):
    super(Permute, self).__init__("Permute")

  def execute(self, voexec, u, v, ell):
    n = voexec.vector_size
    zeta = Symbol(get_name("zeta"))
    voexec.verifier_send_randomness(zeta)
    voexec.run_subprotocol(ProductEq(), u + zeta * PowerVector(1, ell),
                                        v + zeta * PowerVector(1, ell),
                                        ell)


class TriplePermute(VOProtocol):
  def __init__(self):
    super(TriplePermute, self).__init__("Permute")

  def execute(self, voexec, u1, u2, u3, v1, v2, v3, ell):
    n = voexec.vector_size
    zeta = Symbol(get_name("zeta"))
    voexec.verifier_send_randomness(zeta)
    voexec.run_subprotocol(TripleProductEq(), u1 + zeta * PowerVector(1, ell),
                           u2 + zeta * PowerVector(1, ell),
                           u3 + zeta * PowerVector(1, ell),
                           v1 + zeta * PowerVector(1, ell),
                           v2 + zeta * PowerVector(1, ell),
                           v3 + zeta * PowerVector(1, ell),
                           ell)


class CopyCheck(VOProtocol):
  def __init__(self):
    super(CopyCheck, self).__init__("CopyCheck")

  def preprocess(self, voexec, ell):
    vsigma = get_named_vector("sigma")
    voexec.preprocess_latex(Math(vsigma).assign(
        ExpressionVector(gamma ** (Symbol("\\sigma(i)")-1), ell)
    ))
    voexec.preprocess_vector(vsigma, ell)
    voexec.preprocess_output_pk(vsigma)
    voexec.vsigma = vsigma
    voexec.ell = ell

  def execute(self, voexec, v):
    n, ell = voexec.vector_size, voexec.ell
    zeta = Symbol(get_name("zeta"))
    voexec.verifier_send_randomness(zeta)
    voexec.run_subprotocol(Permute(), v + zeta * PowerVector(gamma, ell),
                           v + zeta * voexec.vsigma, ell)


class TripleCopyCheck(VOProtocol):
  def __init__(self):
    super(TripleCopyCheck, self).__init__("CopyCheck")

  def preprocess(self, voexec, ell):
    vsigma1 = get_named_vector("sigma")
    vsigma2 = get_named_vector("sigma")
    vsigma3 = get_named_vector("sigma")
    voexec.preprocess(Math(vsigma1).assign(
        ExpressionVector(gamma ** (Symbol("\\sigma(i)")-1), ell)
    ))
    voexec.preprocess(Math(vsigma2).assign(
        ExpressionVector(gamma ** (Symbol("\\sigma(i+%s)" % tex(ell))-1), ell)
    ))
    voexec.preprocess(Math(vsigma3).assign(
        ExpressionVector(
            gamma ** (Symbol("\\sigma(i+%s)" % tex(2*ell))-1), ell)
    ))
    voexec.preprocess_vector(vsigma1, ell)
    voexec.preprocess_vector(vsigma2, ell)
    voexec.preprocess_vector(vsigma3, ell)
    voexec.preprocess_output_pk(vsigma1)
    voexec.preprocess_output_pk(vsigma2)
    voexec.preprocess_output_pk(vsigma3)
    voexec.vsigma1 = vsigma1
    voexec.vsigma2 = vsigma2
    voexec.vsigma3 = vsigma3
    voexec.ell = ell

  def execute(self, voexec, a, b, c):
    n, ell = voexec.vector_size, voexec.ell
    zeta = Symbol(get_name("zeta"))
    voexec.verifier_send_randomness(zeta)
    voexec.run_subprotocol(TriplePermute(), a + zeta * PowerVector(gamma, ell),
                           b + zeta * (gamma ** ell) * PowerVector(gamma, ell),
                           c + zeta * (gamma ** (2 * ell)) *
                           PowerVector(gamma, ell),
                           a + zeta * voexec.vsigma1,
                           b + zeta * voexec.vsigma2,
                           c + zeta * voexec.vsigma3, ell)


class POV(VOProtocol):
  def __init__(self):
    super(POV, self).__init__("POV")

  def preprocess(self, voexec, d, Cc, Ca, Cm):
    C = Cc + Ca + Cm
    CopyCheck().preprocess(voexec, 3 * C)
    voexec.preprocess_vector(d, Cc)
    voexec.preprocess_output_pk(d)
    voexec.Ca = Ca
    voexec.Cm = Cm
    voexec.Cc = Cc
    voexec.C = C
    voexec.d = d

  def execute(self, voexec, x, a, b, c):
    voexec.input_instance(x)
    voexec.input_witness(a)
    voexec.input_witness(b)
    voexec.input_witness(c)

    C, Cc, Ca, Cm, d, n = voexec.C, voexec.Cc, voexec.Ca, voexec.Cm, voexec.d, voexec.vector_size
    w = get_named_vector("w")
    voexec.prover_computes_latex(Math(w).assign(a.slice(Cc+1, C)).double_bar(b)
                           .double_bar(c))
    voexec.prover_submit_vector(w, 3 * C - Cc)
    t = get_named_vector("t")
    t.local_evaluate = True
    voexec.verifier_computes(Math(t).assign("\\sum_{i\\in\\cI_x}%s"
                                            % UnitVector(Symbol("i")).dumps()))
    voexec.hadamard_query(
        w.shift(n-Cm),
        w.shift(n-Cm-C),
        PowerVector(1, Cm).shift(n-Cm),
        w.shift(n-Cm-2*C),
    )
    voexec.hadamard_query(
        PowerVector(1, Ca).shift(2*C+Cm),
        w.shift(C*2) + w.shift(C) - w,
    )
    voexec.hadamard_query(t, w.shift(Cc) - x)
    voexec.hadamard_query(
        PowerVector(1, Cc).shift(C+Ca+Cm),
        w - d.shift(C+Ca+Cm),
    )
    voexec.run_subprotocol(CopyCheck(), w.shift(Cc))


class POVProverEfficient(VOProtocol):
  def __init__(self):
    super(POVProverEfficient, self).__init__("POVProverEfficient")

  def preprocess(self, voexec, d, Cc, Ca, Cm):
    C = Cc + Ca + Cm
    TripleCopyCheck().preprocess(voexec, C)
    voexec.preprocess_vector(d, Cc)
    voexec.preprocess_output_pk(d)
    voexec.Ca = Ca
    voexec.Cm = Cm
    voexec.Cc = Cc
    voexec.C = C
    voexec.d = d

  def execute(self, voexec, x, a, b, c):
    voexec.input_instance(x)
    voexec.input_witness(a)
    voexec.input_witness(b)
    voexec.input_witness(c)

    C, Cc, Ca, Cm, d = voexec.C, voexec.Cc, voexec.Ca, voexec.Cm, voexec.d
    ap = get_named_vector("a")
    bm = get_named_vector("b")
    bp = get_named_vector("b")
    cp = get_named_vector("c")
    s = get_named_vector("s")
    voexec.prover_computes_latex(Math(ap).assign(a.slice(Cc+1, C)))
    voexec.prover_computes_latex(Math(bm).assign(
        b.slice(Cc+1, Cc+Cm)))
    voexec.prover_computes_latex(Math(bp).assign(b.slice(Cc+Cm, C)))
    voexec.prover_computes_latex(Math(cp).assign(c.slice(Cc+1, C)))

    voexec.prover_submit_vector(ap, Ca+Cm)
    voexec.prover_submit_vector(bp, Ca)
    voexec.prover_submit_vector(bm, Cm)
    voexec.prover_submit_vector(cp, Ca+Cm)

    x1 = get_named_vector("x")
    x2 = get_named_vector("x")
    x3 = get_named_vector("x")
    x1.local_evaluate = True
    x2.local_evaluate = True
    x3.local_evaluate = True
    voexec.verifier_computes(Math(x1).assign(x.slice(1, C)))
    voexec.verifier_computes(Math(x2).assign(x.slice(C+1, 2*C)))
    voexec.verifier_computes(Math(x3).assign(x.slice(2*C+1, 3*C)))

    t1 = get_named_vector("t")
    t2 = get_named_vector("t")
    t3 = get_named_vector("t")
    t1.local_evaluate = True
    t2.local_evaluate = True
    t3.local_evaluate = True
    voexec.verifier_computes(Math(t1).assign("\\sum_{i\\in\\cI_x\\cap[C]}%s"
                                             % UnitVector(Symbol("i")).dumps()))
    voexec.verifier_computes(Math(t2).assign("\\sum_{i\\in\\cI_x\\cap[C+1..2C]}%s"
                                             % UnitVector(Symbol("i")).dumps()))
    voexec.verifier_computes(Math(t3).assign("\\sum_{i\\in\\cI_x\\cap[2C+1..3C]}%s"
                                             % UnitVector(Symbol("i")).dumps()))

    voexec.hadamard_query(PowerVector(1, Ca).shift(Cm),
                          bm, PowerVector(1, Cm), bp)
    voexec.hadamard_query(
        PowerVector(1, Ca),
        ap + bp - cp,
    )
    voexec.hadamard_query(ap, bm, PowerVector(1, Cm), cp)
    voexec.hadamard_query(t1, ap.shift(Cc) - x1)
    voexec.hadamard_query(t2, bp.shift(Cc) - x2)
    voexec.hadamard_query(t3, cp.shift(Cc) - x3 + d)
    voexec.run_subprotocol(TripleCopyCheck(), ap.shift(
        Cc), (bm+bp).shift(Cc), cp.shift(Cc) + d)
