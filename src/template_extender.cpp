#include "template_extender.h"

#include "enumerator.h"

using namespace std;

int count_sort_usage(
    shared_ptr<Value> v,
    lsort so)
{
  assert(v.get() != NULL);
  if (Forall* val = dynamic_cast<Forall*>(v.get())) {
    return count_sort_usage(val->body, so);
  }
  else if (Exists* val = dynamic_cast<Exists*>(v.get())) {
    return count_sort_usage(val->body, so);
  }
  else if (NearlyForall* val = dynamic_cast<NearlyForall*>(v.get())) {
    return count_sort_usage(val->body, so);
  }
  else if (Var* val = dynamic_cast<Var*>(v.get())) {
    if (sorts_eq(val->sort, so)) {
      return 1;
    } else {
      return 0;
    }
  }
  else if (Const* val = dynamic_cast<Const*>(v.get())) {
    return 0;
  }
  else if (Eq* val = dynamic_cast<Eq*>(v.get())) {
    return count_sort_usage(val->left, so)
         + count_sort_usage(val->right, so);
  }
  else if (Not* val = dynamic_cast<Not*>(v.get())) {
    return count_sort_usage(val->val, so);
  }
  else if (Implies* val = dynamic_cast<Implies*>(v.get())) {
    return count_sort_usage(val->left, so)
         + count_sort_usage(val->right, so);
  }
  else if (Apply* ap = dynamic_cast<Apply*>(v.get())) {
    int c = count_sort_usage(ap->func, so);
    for (value arg : ap->args) {
      c += count_sort_usage(arg, so);
    }
    return c;
  }
  else if (And* a = dynamic_cast<And*>(v.get())) {
    int c = 0;
    for (value arg : a->args) {
      c += count_sort_usage(arg, so);
    }
    return c;
  }
  else if (Or* o = dynamic_cast<Or*>(v.get())) {
    int c = 0;
    for (value arg : o->args) {
      c += count_sort_usage(arg, so);
    }
    return c;
  }
  else if (IfThenElse* val = dynamic_cast<IfThenElse*>(v.get())) {
    return count_sort_usage(val->cond, so)
         + count_sort_usage(val->then_value, so)
         + count_sort_usage(val->else_value, so);
  }
  else {
    assert(false && "count_sort_usage does not support this case");
  }
}

int tgenname_idx = 0;
iden get_template_variable_name() {
  tgenname_idx++;
  return string_to_iden("_templ_" + to_string(tgenname_idx));
}

value template_from_counts(shared_ptr<Module> module, map<string, int> const& sort_to_count)
{
  vector<VarDecl> decls;
  for (string so : module->sorts) {
    if (sort_to_count.count(so)) {
      lsort sor = s_uninterp(so);
      int c = sort_to_count.find(so)->second;
      for (int i = 0; i < c; i++) {
        decls.push_back(VarDecl(get_template_variable_name(), sor));
      }
    }
  }
  return v_forall(decls, v_template_hole());
}

value extend_template(shared_ptr<Module> module, value templ, int n)
{
  auto values = cached_get_unfiltered_values(module, 1);
  values->init_simp();
  vector<value> pieces = values->values;

  map<string, int> sort_to_count;

  for (string so : module->sorts) {
    int m = 0;
    for (value p : pieces) {
      m = max(m, count_sort_usage(p, s_uninterp(so)));
    }
    sort_to_count[so] = n*m;
  }

  return template_from_counts(module, sort_to_count);
}

