#ifndef EXTRA_ENUMERATOR_H
#define EXTRA_ENUMERATOR_H

#include <cassert>

#include "synth_enumerator.h"

class ExtraCandidateEnumerator {
public:
  value getNext();
  void addCounterexample(Counterexample cex) {
    assert (!cex.is_false);
    cexes.push_back(cex);
  }
  void addExistingInvariant(value inv) { }
  void filterOutdatedCexes(value inv);

  void addExtras(std::vector<value> const& new_candidates);

private:
  std::vector<value> candidates;
  std::vector<Counterexample> cexes;

  bool passes_all_cexes(value);
};

#endif
