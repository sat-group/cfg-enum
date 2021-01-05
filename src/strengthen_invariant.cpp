#include "strengthen_invariant.h"

#include "top_quantifier_desc.h"
#include "contexts.h"

using namespace std;

vector<value> remove(vector<value> const& ar, int j) {
  vector<value> v;
  for (int i = 0; i < (int)ar.size(); i++) {
    if (i != j) {
      v.push_back(ar[i]);
    }
  }
  return v;
}

vector<value> replace(vector<value> const& ar, int j, value newv) {
  assert(0 <= j && j < (int)ar.size());
  vector<value> v = ar;
  v[j] = newv;
  return v;
}

value try_replacing_exists_with_forall(
  shared_ptr<Module> module,
  value invariant_so_far,
  value new_invariant)
{
  TopAlternatingQuantifierDesc taqd(new_invariant);
  value body = TopAlternatingQuantifierDesc::get_body(new_invariant);
  TopAlternatingQuantifierDesc taqd_mod = taqd.replace_exists_with_forall();

  value inv0 = taqd_mod.with_body(body);

  if (is_invariant_wrt_tryhard(module, invariant_so_far, inv0)) {
    return inv0;
  }

  return new_invariant;
}

value strengthen_invariant_once(
  shared_ptr<Module> module,
  value invariant_so_far,
  value new_invariant)
{
  new_invariant = try_replacing_exists_with_forall(module, invariant_so_far, new_invariant);

  TopAlternatingQuantifierDesc taqd(new_invariant);
  value body = TopAlternatingQuantifierDesc::get_body(new_invariant);

  Or* disj = dynamic_cast<Or*>(body.get());
  if (!disj) {
    return new_invariant;
  }
  vector<value> args = disj->args;

  //cout << endl;

  for (int i = 0; i < (int)args.size(); i++) {
    vector<value> new_args = remove(args, i);
    value inv = taqd.with_body(v_or(new_args));
    //cout << "trying " << inv->to_string();
    if (is_invariant_wrt_tryhard(module, invariant_so_far, inv)) {
      //cout << "is inv" << endl << endl;
      args = new_args;
      i--;
    } else {
      //cout << "is not inv" << endl << endl;
    }
  }

  for (int i = 0; i < (int)args.size(); i++) {
    //cout << "i = " << i << endl;
    if (And* a = dynamic_cast<And*>(args[i].get())) {
      for (int j = 0; j < (int)a->args.size(); j++) {
        //cout << "j = " << j << endl;
        vector<value> new_conj = remove(a->args, j);
        vector<value> new_args = replace(args, i, v_and(new_conj));
        value inv0 = taqd.with_body(v_or(args));
        value inv1 = taqd.with_body(v_or(new_args));
        if (!is_satisfiable(module, v_and({invariant_so_far, inv1, v_not(inv0)}))
            && is_invariant_wrt_tryhard(module, invariant_so_far, inv1)) {
          //cout << "is inv (and implies)" << endl << endl;
          args = new_args;
          a = dynamic_cast<And*>(args[i].get());
          if (a == NULL) {
            break;
          }
          j--;
          //cout << "done with j = " << j << endl;
          //cout << "a->args.size() " << a->args.size() << endl;
        } else {
          //cout << "is not inv or not implies" << endl << endl;
        }
      }
      //cout << "done with i = " << i << endl;
    }
  }

  return taqd.with_body(v_or(args));
}

value strengthen_invariant(
  shared_ptr<Module> module,
  value invariant_so_far,
  value new_invariant)
{
  //cout << "strengthening " << new_invariant->to_string() << endl;
  value inv = new_invariant;

  int t = 0;
  while (true) {
    assert (t < 20);

    value inv0 = strengthen_invariant_once(module, invariant_so_far, inv);
    if (v_eq(inv, inv0)) {
      //cout << "got " << inv0->to_string() << endl;
      return inv0;
    }
    inv = inv0;
  }
}

std::vector<value> get_all_strengthened(
    std::shared_ptr<Module> module,
    value v)
{
  TopAlternatingQuantifierDesc taqd(v);
  bool any_exists = taqd.has_any_exists();
  TopAlternatingQuantifierDesc taqd_mod = taqd.replace_exists_with_forall();

  value body = TopAlternatingQuantifierDesc::get_body(v);

  vector<value> args;
  Or* disj = dynamic_cast<Or*>(body.get());
  if (!disj) {
    args.push_back(body);
  } else {
    args = disj->args;
  }
  int n = args.size();

  vector<value> results;

  for (int mask = (1 << n) - 1; mask >= 1; mask--) {
    for (int remove_es = 0; remove_es < 2; remove_es++) {
      if (remove_es && !any_exists) {
        continue;
      }
      if (!remove_es && mask == ((1 << n) - 1)) {
        continue;
      }

      vector<value> sub_args;
      for (int j = 0; j < n; j++) {
        if ((mask >> j) & 1) {
          sub_args.push_back(args[j]);
        }
      }

      value new_v;
      if (remove_es) {
        new_v = taqd_mod.with_body(v_or(sub_args));
      } else {
        new_v = taqd.with_body(v_or(sub_args));
      }

      results.push_back(new_v);
    }
  }

  return results;
}
