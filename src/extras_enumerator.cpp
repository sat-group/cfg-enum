#include "extras_enumerator.h"

using namespace std;

void ExtraCandidateEnumerator::addExtras(std::vector<value> const& new_candidates)
{
  int cur_size = candidates.size();

  for (value c : new_candidates) {
    bool is_new = true;
    for (int i = 0; i < cur_size; i++) {
      if (values_equal(candidates[i], c)) {
        is_new = false;
        break;
      }
    }
    if (is_new) {
      candidates.push_back(c);
    }
  }
}

bool ExtraCandidateEnumerator::passes_all_cexes(value v)
{
  for (Counterexample const& cex : cexes) {
    if (cex.is_true) {
      if (!cex.is_true->eval_predicate(v)) {
        return false;
      }
    } else {
      if (cex.hypothesis->eval_predicate(v)
          && !cex.conclusion->eval_predicate(v)) {
        return false;
      }
    }
  }
  return true;
}

value ExtraCandidateEnumerator::getNext()
{
  int i;
  value res = nullptr;
  for (i = 0; i < (int)candidates.size(); i++) {
    if (passes_all_cexes(candidates[i])) {
      res = candidates[i];
      i++;
      break;
    }
  }

  candidates.erase(candidates.begin(), candidates.begin() + i);

  return res;
}

bool is_outdated(Counterexample const& cex, value new_inv)
{
  // Any true-type cex will still be okay, and we're assuming no false-types,
  // so we only have to check the inductive-type case.
  //
  // For the inductive-type case,
  // `cex` is only valid (i.e., not outdated) if:
  //
  // (i) `INV & new_inv` evalutes to true on `hypothesis`
  // (ii) `INV & new_inv` evalutes to false on `conclusion`
  //
  // We already have that
  //
  // `INV` evalutes to true on `hypothesis`
  // `INV` evalutes to false on `conclusion`
  //
  // Thus (ii) will definitely hold, we just need to check (i) by
  // checking new_inv on the `hypothesis`

  return cex.hypothesis && !cex.hypothesis->eval_predicate(new_inv);
}

void ExtraCandidateEnumerator::filterOutdatedCexes(value inv) {
  int cur = 0;
  for (int i = 0; i < (int)cexes.size(); i++) {
    if (is_outdated(cexes[i], inv)) {
    } else {
      if (cur < i) {
        cexes[cur] = cexes[i];
      }
      cur++;
    }
  }
  cexes.resize(cur);
}
