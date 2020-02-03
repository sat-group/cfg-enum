#include "strengthen_invariant.h"

#include "top_quantifier_desc.h"
#include "contexts.h"

using namespace std;

vector<value> remove(vector<value> const& ar, int j) {
  vector<value> v;
  for (int i = 0; i < ar.size(); i++) {
    if (i != j) {
      v.push_back(ar[i]);
    }
  }
  return v;
}

value strengthen_invariant_remove_disjuncts(
  shared_ptr<Module> module,
  value invariant_so_far,
  value new_invariant)
{
  TopQuantifierDesc tqd(new_invariant);

  value body = new_invariant;
  while (true) {
    if (Forall* f = dynamic_cast<Forall*>(body.get())) {
      body = f->body;
    }
    else if (NearlyForall* f = dynamic_cast<NearlyForall*>(body.get())) {
      body = f->body;
    }
    else {
      break;
    }
  }

  Or* disj = dynamic_cast<Or*>(body.get());
  if (!disj) {
    return new_invariant;
  }
  vector<value> args = disj->args;

  for (int i = 0; i < args.size(); i++) {
    vector<value> new_args = remove(args, i);
    value inv = tqd.with_body(v_or(new_args));
    if (is_invariant_wrt(module, invariant_so_far, inv)) {
      args = new_args;
      i--;
    }
  }

  return tqd.with_body(v_or(args));
}

void get_nullary_consts_(value v, vector<value>& res) {
  assert(v.get() != NULL);
  if (Forall* va = dynamic_cast<Forall*>(v.get())) {
    get_nullary_consts_(va->body, res);
  }
  else if (Exists* va = dynamic_cast<Exists*>(v.get())) {
    get_nullary_consts_(va->body, res);
  }
  else if (Var* va = dynamic_cast<Var*>(v.get())) {
    return;
  }
  else if (Const* va = dynamic_cast<Const*>(v.get())) {
    if (va->sort->get_domain_as_function().size() == 0) {
      res.push_back(v);
    }
    return;
  }
  else if (Eq* va = dynamic_cast<Eq*>(v.get())) {
    get_nullary_consts_(va->left, res);
    get_nullary_consts_(va->right, res);
  }
  else if (Not* va = dynamic_cast<Not*>(v.get())) {
    get_nullary_consts_(va->val, res);
  }
  else if (Implies* va = dynamic_cast<Implies*>(v.get())) {
    get_nullary_consts_(va->left, res);
    get_nullary_consts_(va->right, res);
  }
  else if (Apply* va = dynamic_cast<Apply*>(v.get())) {
    get_nullary_consts_(va->func, res);
    for (value arg : va->args) {
      get_nullary_consts_(arg, res);
    }
  }
  else if (And* va = dynamic_cast<And*>(v.get())) {
    for (value arg : va->args) {
      get_nullary_consts_(arg, res);
    }
  }
  else if (Or* va = dynamic_cast<Or*>(v.get())) {
    for (value arg : va->args) {
      get_nullary_consts_(arg, res);
    }
  }
  else if (TemplateHole* value = dynamic_cast<TemplateHole*>(v.get())) {
  }
  else {
    assert(false && "get_nullary_consts_ does not support this case");
  }
}

vector<value> get_nullary_consts(value v) {
  vector<value> res;
  get_nullary_consts_(v, res);
  return res;
}

int genname_idx = 0;
iden get_generalized_variable_name() {
  genname_idx++;
  return string_to_iden("_generalized_" + to_string(genname_idx));
}

value generalize_const(value inv, iden id, lsort so) {
  iden gen_var_id = get_generalized_variable_name();

  //value r = replace_const_with(id, v_var(gen_var_id, so));
  map<iden, iden> substs;
  substs.insert(make_pair(id, gen_var_id));
  value r = inv->replace_const_with_var(substs);

  VarDecl decl(gen_var_id, so);
  if (Forall* f = dynamic_cast<Forall*>(r.get())) {
    vector<VarDecl> decls = f->decls;
    decls.push_back(decl);
    return v_forall(decls, f->body);
  } else {
    return v_forall({decl}, r);
  }
}

value strengthen_invariant_generalize_consts(
  shared_ptr<Module> module,
  value invariant_so_far,
  value new_invariant)
{
  vector<value> consts = get_nullary_consts(new_invariant);
  value inv = new_invariant;
  for (value v : consts) {
    Const* c = dynamic_cast<Const*>(v.get());
    assert(c != NULL);
    value gen = generalize_const(new_invariant, c->name, c->sort);
    if (is_invariant_wrt(module, invariant_so_far, gen)) {
      inv = gen;
    }
  }
  return inv;
}

value strengthen_invariant(
  shared_ptr<Module> module,
  value invariant_so_far,
  value new_invariant)
{
  value inv = new_invariant;
  inv = strengthen_invariant_remove_disjuncts(
      module, invariant_so_far, inv);
  inv = strengthen_invariant_generalize_consts(
      module, invariant_so_far, inv);
  return inv;
}

vector<value> get_consts_for_sort(shared_ptr<Module> module, lsort so)
{
  vector<value> res;
  for (VarDecl const& decl : module->functions) {
    if (decl.sort->get_domain_as_function().size() == 0) {
      res.push_back(v_const(decl.name, decl.sort));
    }
  }
  return res;
}

vector<value> specialize_invariant(shared_ptr<Module> module, value v)
{
  if (Forall* f = dynamic_cast<Forall*>(v.get())) {
    VarDecl decl = f->decls[0];
    value body;
    if (f->decls.size() == 1) {
      body = f->body;
    } else {
      vector<VarDecl> subdecls = f->decls;
      subdecls.erase(subdecls.begin());
      body = v_forall(subdecls, f->body);
    }

    vector<value> subresults = specialize_invariant(module, body);
    vector<value> results;

    vector<value> consts_for_sort =
        get_consts_for_sort(module, decl.sort);

    for (value sub : subresults) {
      results.push_back(forall_append(decl, sub));
      for (value con : consts_for_sort) {
        results.push_back(sub->subst(decl.name, con));
      }
    }

    return results;
  } else {
    return {v};
  }
}
