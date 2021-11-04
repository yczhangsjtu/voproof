from sympy import Symbol, latex, sympify, Integer, simplify
from os.path import basename
from sympy.abc import alpha, beta, gamma, X, D, S
from optimized_compiler import VOProtocol, PIOPExecution, PIOPFromVOProtocol, \
                               ZKSNARKFromPIOPExecKZG, VOProtocolExecution, \
                               ProverComputes, VerifierComputes
from vector_symbol import get_named_vector, reset_name_counters, get_name
from smvp_protocols import SparseMVP, SparseMVPProverEfficient, \
                           R1CS, R1CSProverEfficient, \
                           HPR, HPRProverEfficient
from pov_protocols import POV, POVProverEfficient
from rust_builder import RustBuilder, rust, RustMacro
from latex_builder import LaTeXBuilder

ell = Symbol("ell", positive=True)
m = Symbol("m", positive=True)
# n = Symbol("n", positive=True)
H = Symbol("H", positive=True)
K = Symbol("K", positive=True)
s = Symbol("s", positive=True)

Cc = Symbol("C_c", positive=True)
Ca = Symbol("C_a", positive=True)
Cm = Symbol("C_m", positive=True)
Sa = Symbol("S_a", positive=True)
Sb = Symbol("S_b", positive=True)
Sc = Symbol("S_c", positive=True)

k = Symbol("k", positive=True)

def dump_performance(piopexec, zkSNARK, name):
  voexec = piopexec.reference_to_voexec
  print("%s preprocessed polynomials: %d" % (name, len(piopexec.indexer_polynomials)))
  print("%s online polynomials: %d" % (name, len(piopexec.prover_polynomials)))
  n_distinct = len(piopexec.distinct_points)
  print("%s distinct points: %d" % (name, n_distinct))
  n_evals = len(piopexec.eval_queries) + len(piopexec.eval_checks)
  print("%s eval queries: %d" % (name, n_evals))
  print("%s max degree: %s" % (name, latex(piopexec.max_degree)))
  print("%s minimal n: %s" % (name, latex(voexec.vector_size_bound)))
  n_field_elements = len([p for p in zkSNARK.proof if latex(p).startswith("y")])
  print("%s proof size: %d G + %d F" %
        (name, len(zkSNARK.proof) - n_field_elements, n_field_elements))
  c_g_exps = sum([len(poly_combine.coeff_latex_builders)
                 for poly_combine in piopexec.poly_combines])
  v_g_exps = n_evals + 2 * n_distinct - 2 + c_g_exps
  print("%s verifier G-exps: %d" % (name, v_g_exps))
  p_g_exps = c_g_exps + piopexec.max_degree * 4 + voexec.vector_size_sum
  print("%s prover G-exps: %s" % (name, latex(p_g_exps)))
  print()


def get_minimal_vector_size(protocol, ppargs, execargs, simplify_hints):
  voexec = VOProtocolExecution(Symbol("N"))
  voexec._simplify_max_hints = simplify_hints
  protocol.preprocess(voexec, *ppargs)
  protocol.execute(voexec, *execargs)
  reset_name_counters()
  return voexec.vector_size_bound

def analyzeProtocol(protocol, ppargs, execargs, simplify_hints, size_map, filename=None):
  name = protocol.__class__.__name__
  n = get_minimal_vector_size(protocol, ppargs, execargs, simplify_hints)
  debug("Start analyzing %s..." % name)
  piop = PIOPFromVOProtocol(protocol, n, D)
  piop.debug_mode = debug_mode
  debug("Start preprocessing...")
  piopexec = PIOPExecution()
  size_init = RustBuilder()
  for size, value in size_map:
    size_init.let(size).assign("size.%s as i64" % value).end()

  compute_init = RustBuilder().let(gamma).assign("generator_of!(E)").end()
  piop.preprocess(piopexec, *ppargs)
  piopexec.reference_to_voexec._simplify_max_hints = simplify_hints
  debug("Start executing...")
  piop.execute(piopexec, *execargs)
  piopexec.max_degree = piopexec.reference_to_voexec.simplify_max(piopexec.max_degree)

  debug("Start compiling to zkSNARK...")
  zkSNARK = ZKSNARKFromPIOPExecKZG(piopexec)
  zkSNARK.indexer_computations =  [
      VerifierComputes(LaTeXBuilder(), size_init),
      VerifierComputes(LaTeXBuilder(), compute_init)] + zkSNARK.indexer_computations
  zkSNARK.verifier_computations = [
      VerifierComputes(LaTeXBuilder(), size_init),
      VerifierComputes(LaTeXBuilder(), compute_init)] + zkSNARK.verifier_computations
  zkSNARK.prover_computations = [
      ProverComputes(LaTeXBuilder(), size_init),
      ProverComputes(LaTeXBuilder(), compute_init)] + zkSNARK.prover_computations
  debug()
  dump_performance(piopexec, zkSNARK, name)

  if filename is not None:
    with open("../snarks/template.rs") as template:
      temp = template.readlines()
    temp = [line.replace("__NAME__", name) for line in temp]
    size_mark = "/*{size}*/"
    vk_definition_mark, vk_return_mark = "/*{VerifierKey}*/", "/*{index verifier key}*/"
    pk_definition_mark, pk_return_mark = "/*{ProverKey}*/", "/*{index prover key}*/"
    proof_definition_mark, proof_return_mark = "/*{Proof}*/", "/*{proof}*/"
    indexer_mark, prover_mark, verifier_mark = "/*{index}*/", "/*{prove}*/", "/*{verify}*/"
    indexer_code, prover_code, verifier_code = \
        zkSNARK.dump_indexer_rust(), zkSNARK.dump_prover_rust(), \
        zkSNARK.dump_verifier_rust()
    verifier_key_definition = zkSNARK.dump_vk_definition()
    prover_key_definition = zkSNARK.dump_pk_definition()
    proof_definition = zkSNARK.dump_proof_definition()
    verifier_key_construction = zkSNARK.dump_vk_construction()
    prover_key_construction = zkSNARK.dump_pk_construction()
    proof_construction = zkSNARK.dump_proof_construction()
    for i in range(len(temp)):
      if size_mark in temp[i]:
        temp[i] = temp[i].replace(size_mark, "%s\n        (%s) as usize" % 
                                             (rust(size_init), str(piopexec.max_degree)))
      if vk_definition_mark in temp[i]:
        temp[i] = temp[i].replace(vk_definition_mark, verifier_key_definition)
      if pk_definition_mark in temp[i]:
        temp[i] = temp[i].replace(pk_definition_mark, prover_key_definition)
      if proof_definition_mark in temp[i]:
        temp[i] = temp[i].replace(proof_definition_mark, proof_definition)
      if vk_return_mark in temp[i]:
        temp[i] = temp[i].replace(vk_return_mark, verifier_key_construction)
      if pk_return_mark in temp[i]:
        temp[i] = temp[i].replace(pk_return_mark, prover_key_construction)
      if proof_return_mark in temp[i]:
        temp[i] = temp[i].replace(proof_return_mark, proof_construction)
      if indexer_mark in temp[i]:
        temp[i] = temp[i].replace(indexer_mark, indexer_code)
      if prover_mark in temp[i]:
        temp[i] = temp[i].replace(prover_mark, prover_code)
      if verifier_mark in temp[i]:
        temp[i] = temp[i].replace(verifier_mark, verifier_code)
    temp = "".join(temp)

    with open("../snarks/%s.rs" % filename, "w") as f:
      print("///! This file is generated by scripts/%s"
            % basename(__file__), file=f)
      print(temp, file=f);

  reset_name_counters()


def analyzeR1CS():
  hints = [(H, K), (Sa, K + 1), (Sa, H + 1), (Sb, K + 1), (Sb, H + 1), (Sc, K + 1), (Sc, H + 1),
           (Sa + Sb + Sc, 3 * K + 3), (Sa + Sb + Sc, 3 * H + 3)]
  size_map = [(H, "nrows"), (K, "ncols"),
              (Sa, "adensity"), (Sb, "bdensity"), (Sc, "cdensity"),
              (ell, "input_size")]
  x = get_named_vector("x")
  x.local_evaluate = True
  x.hint_computation = lambda z: RustMacro("eval_vector_expression").append([
        z, Symbol("i"), x.dumpr_at_index(Symbol("i")), ell
      ])
  ppargs = (H, K, Sa, Sb, Sc)
  execargs = (x, get_named_vector("w"), ell)
  analyzeProtocol(R1CS(), ppargs, execargs, hints, size_map, filename="voproof_r1cs")

def analyzeR1CSProverEfficient():
  hints = [(S, H + 1), (S, K + 1), (H, K)]
  size_map = [(H, "nrows"), (K, "ncols"), (S, "density")]
  x = get_named_vector("x")
  x.local_evaluate = True
  ppargs = (H, K, S*3)
  execargs = (x, get_named_vector("w"), ell)
  analyzeProtocol(R1CSProverEfficient(), ppargs, execargs, hints, size_map)

def analyzeHPR():
  Sp = Symbol(get_name("S'"), positive=True)
  hints = [(S, H + 1), (S, K + 1), (H, Sp), (K, ell), (H, ell), (S, ell + 1)]
  size_map = [(H, "nrows"), (K, "ncols"), (S, "density"), (Sp, "d_density")]
  x = get_named_vector("x")
  x.local_evaluate = True
  ppargs = (H, K, S*3+Sp)
  execargs = (x, get_named_vector("w"), get_named_vector("w"), get_named_vector("w"), ell)
  analyzeProtocol(HPR(), ppargs, execargs, hints, size_map, filename="voproof_hpr")

def analyzeHPRProverEfficient():
  Sp = Symbol(get_name("S'"), positive=True)
  hints = [(S, H + 1), (S, K + 1), (H, Sp), (K, ell), (H, ell), (S, ell + 1), (H, K)]
  size_map = [(H, "nrows"), (K, "ncols"), (S, "density"), (Sp, "d_density")]
  x = get_named_vector("x")
  x.local_evaluate = True
  ppargs = (H, K, S*3+Sp)
  execargs = (x, get_named_vector("w"), get_named_vector("w"), get_named_vector("w"), ell)
  analyzeProtocol(HPRProverEfficient(), ppargs, execargs, hints, size_map)

def analyzePOV():
  C = Symbol(get_name("C"), positive=True)
  hints = [(C, Ca + Cm + 1), (C, 1), (Ca, 1), (Cm, 1)]
  size_map = [(C, "nconsts + size.nadd + size.nmul"), (Ca, "nadd"), (Cm, "nmul"), (Cc, "nconsts")]
  x = get_named_vector("x")
  x.local_evaluate = True
  ppargs = (get_named_vector("d"), C - Ca - Cm, Ca, Cm)
  execargs = (x, get_named_vector("a"), get_named_vector("b"), get_named_vector("c"))
  analyzeProtocol(POV(), ppargs, execargs, hints, size_map, filename="voproof_pov")

def analyzePOVProverEfficient():
  C = Symbol(get_name("C"), positive=True)
  hints = [(C, Ca + Cm + 1), (C, 1), (Ca, 1), (Cm, 1)]
  size_map = [(C, "nconsts + size.nadd + size.nmul"), (Ca, "nadd"), (Cm, "nmul"), (Cc, "nconsts")]
  x = get_named_vector("x")
  x.local_evaluate = True
  ppargs = (get_named_vector("d"), C - Ca - Cm, Ca, Cm)
  execargs = (x, get_named_vector("a"), get_named_vector("b"), get_named_vector("c"))
  analyzeProtocol(POVProverEfficient(), ppargs, execargs, hints, size_map)

debug_mode = True

def debug(info=""):
  if debug_mode:
    print(info)

if __name__ == '__main__':
  # analyzeR1CSProverEfficient()
  # analyzeHPRProverEfficient()
  # analyzePOVProverEfficient()
  analyzeR1CS()
  # analyzeHPR()
  # analyzePOV()

