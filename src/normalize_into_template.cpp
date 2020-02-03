#include "logic.h"
#include "top_quantifier_desc.h"

using namespace std;

struct ScopeMap {
  vector<pair<iden, iden>> varmap;
};

/*value normalize_into_template_(value templ, value val, ScopeMap const& sm)
{
  if (Forall* f_templ = dynamic_cast<Forall*>(templ)) {
    value templ_body = f_templ->body;
    vector<VarDecl> templ_decls = f_templ->decls;

    value val_body;
    vector<VarDecl> val_decls;
    if (Forall* f_val = dynamic_cast<Forall*>(val)) {
      val_body = f_val->body;
      val_decls = f_val->decls;
    } else {
      val_body = val;
    }

    assert(templ_decls.size() > 0);
    if (val_decls.size() == 0) {
      value sub = normalize_into_template_(templ_body, val, sm);
      return v_forall(templ_decls, sub);
    } else {
    }
  }
}*/

value normalize_into_template(shared_ptr<Module> module, value templ, value v) {
  value norm = v->totally_normalize();
  //ScopeMap sm;
  //return normalize_into_template_(templ, norm, sm);

  TopQuantifierDesc templ_tqd(tqd);  
  TopQuantifierDesc v_tqd(v);  

  map<iden, value> substs;
  for (string const& so_name : module->sorts) {
    lsort so = s_uninterp(so_name);
    vector<iden> templ_idens;
    vector<iden> v_idens;
    for (VarDecl decl : templ_tqd.decls()) {
      if (sorts_eq(decl.sort, so)) {
        templ_idens.push_back(decl.name);
      }
    }
    for (VarDecl decl : v_tqd.decls()) {
      if (sorts_eq(decl.sort, so)) {
        v_idens.push_back(decl.name);
      }
    }
    if (templ_idens.size() < v_idens.size()) {
      return nullptr;
    }
    for (int i = 0; i < v_idens.size(); i++) {
      substs.insert(make_pair(v_idens[i], v_var(templ_idens[i], so)));
    }
  }

  value body = v;
  while (Forall* f = dynamic_cast<Forall*>(body.get())) {
    body = f->body;
  }

  return templ_tqd.with_body(body->subst(substs));
}
