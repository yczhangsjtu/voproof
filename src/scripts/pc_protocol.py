from latex_builder import tex, Math
from rust_builder import rust

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

