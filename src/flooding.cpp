#include "flooding.h"

#include <algorithm>

using namespace std;

// TODO start with x | not x
// TODO start with axioms
// TODO start with (exists x . f(x) & not f(y)) and so on
// TODO basic implication: a & (a -> b)
// TODO generalize stuff to existentials
// TODO permute variables
// TODO substitutions in (A=B -> stuff)

Flood::Flood(
    std::shared_ptr<Module> module,
    TemplateSpace const& forall_tspace,
    int max_e)
  : module(module)
  , forall_taqd(v_template_hole())
  , enum_info(nullptr, nullptr)
{
  this->nsorts = module->sorts.size();
  this->max_k = forall_tspace.k;
  this->max_e = max_e;

  value templ = forall_tspace.make_templ(module);
  this->forall_taqd = TopAlternatingQuantifierDesc(templ);
  this->enum_info = EnumInfo(module, templ);

  assert (forall_tspace.depth == 1);

  this->init_piece_to_index();
  this->init_negation_map();
  this->init_masks();
}

std::vector<RedundantDesc> Flood::add_formula(value v)
{
  int initial_entry_len = (int)entries.size();
  int cur = (int)entries.size();

  vector<Entry> new_es = value_to_entries(v);

  for (Entry const& e : new_es) {
    add_checking_subsumes(e);
  }

  while (cur < (int)entries.size()) {
    if (!entries[cur].subsumed) {
      process(entries[cur]);
      for (int j = 0; j < cur; j++) {
        if (!entries[j].subsumed) {
          process2(entries[cur], entries[j]);
        }
      }
    }
    cur++;
  }

  return make_results(initial_entry_len);
}

void Flood::init_piece_to_index() {
  for (int i = 0; i < (int)enum_info.clauses.size(); i++) {
    value v = enum_info.clauses[i];
    while (true) {
      if (Forall* f = dynamic_cast<Forall*>(v.get())) {
        v = f->body;
      }
      else if (Exists* f = dynamic_cast<Exists*>(v.get())) {
        v = f->body;
      }
      else {
        break;
      }
    }
    piece_to_index.insert(make_pair(ComparableValue(v), i));
  }
}

int Flood::get_index_of_piece(value p) {
  auto it = piece_to_index.find(ComparableValue(p));
  if (it == piece_to_index.end()) {
    return -1;
  }
  return it->second;
}

int sort_idx_of_module(std::shared_ptr<Module>& module, lsort so) {
  UninterpretedSort* us = dynamic_cast<UninterpretedSort*>(so.get());
  assert (us != NULL);
  for (int i = 0; i < (int)module->sorts.size(); i++) {
    if (module->sorts[i] == us->name) {
      return i;
    }
  }
  assert(false);
}

bool Flood::get_single_entry_of_value(value inv, vector<int>& t) {
  while (true) {
    if (Forall* f = dynamic_cast<Forall*>(inv.get())) {
      inv = f->body;
    }
    else if (Exists* f = dynamic_cast<Exists*>(inv.get())) {
      inv = f->body;
    }
    else {
      break;
    }
  }
  Or* o = dynamic_cast<Or*>(inv.get());
  if (o != NULL) {
    t.resize(o->args.size());
    for (int i = 0; i < (int)t.size(); i++) {
      int idx = get_index_of_piece(o->args[i]);
      if (idx == -1) { return false; }
      t[i] = idx;
    }
  } else {
    t.resize(1);
    int idx = get_index_of_piece(inv);
    if (idx == -1) { return false; }
    t[0] = idx;
  }
  return true;
}

std::vector<Entry> Flood::value_to_entries(value v)
{
  Entry e;
  e.subsumed = false;
  e.forall_mask = 0;
  e.exists_mask = 0;

  value inv = v;
  while (true) {
    if (Forall* f = dynamic_cast<Forall*>(inv.get())) {
      for (VarDecl const& decl : f->decls) {
        e.forall_mask |= (1 << sort_idx_of_module(module, decl.sort));
      }
      inv = f->body;
    }
    else if (Exists* f = dynamic_cast<Exists*>(inv.get())) {
      for (VarDecl const& decl : f->decls) {
        e.exists_mask |= (1 << sort_idx_of_module(module, decl.sort));
      }
      inv = f->body;
    }
    else {
      break;
    }
  }

  vector<Entry> res;

  std::vector<value> permuted_values =
      forall_taqd.rename_into_all_possibilities_ignore_quantifier_types(v);
  for (value pv : permuted_values) {
    bool success = get_single_entry_of_value(pv, e.v /* output */);
    if (success) {
      res.push_back(e);
    }
  }

  return res;
}

inline bool matches_forall_mask(uint32_t m, uint32_t f)
{
  // need to check that f is disjoint from m
  return (f & m) == 0;
}

inline bool matches_exists_mask(uint32_t m, uint32_t e)
{
  // need to check that e is a subset of m
  return (e | m) == m;
}

std::vector<RedundantDesc> Flood::make_results(int start)
{
  std::vector<RedundantDesc> res;
  for (int i = start; i < (int)entries.size(); i++) {
    for (uint32_t m = 0; m < (1 << nsorts); m++) {
      if (matches_forall_mask(m, entries[i].forall_mask)
        && matches_exists_mask(m, entries[i].exists_mask))
      {
        RedundantDesc rd;
        rd.v = entries[i].v;
        rd.quant_mask = m;
        res.push_back(rd);
      }
    }
  }
  return res;
}

inline bool is_indices_subset(vector<int> const& a, vector<int> const& b)
{
  if (a.size() == 0) { return true; }
  if (b.size() == 0) return false;
  int i = 0;
  int j = 0;
  while (true) {
    if (a[i] < b[j]) {
      return false;
    }
    else if (a[i] == b[j]) {
      i++;
      j++;
      if (i >= (int)a.size()) { return true; }
      if (j >= (int)b.size()) return false;
    }
    else {
      j++;
      if (j >= (int)b.size()) return false;
    }
  }
}

// returns true if e1 <= e2
bool Flood::does_subsume(Entry const& e1, Entry const& e2)
{
  return
      !(e1.forall_mask & e2.exists_mask)
   && !(e2.forall_mask & e1.exists_mask)
   && is_indices_subset(e1.v, e2.v);
}

void Flood::add_checking_subsumes(Entry const& e) {
  if (in_bounds(e)) {
    for (int i = 0; i < (int)this->entries.size(); i++) {
      if (!this->entries[i].subsumed) {
        if (does_subsume(this->entries[i], e)) {
          return;
        } else if (does_subsume(e, this->entries[i])) {
          this->entries[i].subsumed = true;
        }
      }
    }
    this->entries.push_back(e);
  }
}

void Flood::process2(Entry const& a, Entry const& b)
{
  if ((a.forall_mask & b.exists_mask)
   || (a.forall_mask & b.exists_mask)) {
    return;
  }

  process_impl(a, b);
}

void sort_and_remove_dupes(vector<int>& t)
{
  sort(t.begin(), t.end());
  int cur = 1;
  for (int i = 1; i < (int)t.size(); i++) {
    if (t[i] == t[i-1]) {
    } else {
      t[cur] = t[i];
      cur++;
    }
  }
  t.resize(cur);
}

Entry Flood::make_entry(vector<int> const& t, uint32_t forall, uint32_t exists)
{
  Entry e;
  e.v = t;
  sort_and_remove_dupes(e.v);
  e.forall_mask = forall;
  e.exists_mask = exists;
  return e;
}

void Flood::process_impl(Entry const& a, Entry const& b)
{
  if (a.v.size() + b.v.size() <= 2 || (int)a.v.size() + (int)b.v.size() - 2 > max_k) {
    return;
  }
  if (a.v.size() == 2 && are_negations(a.v[0], a.v[1])) {
    return;
  }
  if (b.v.size() == 2 && are_negations(b.v[0], b.v[1])) {
    return;
  }

  for (int i = 0; i < (int)a.v.size(); i++) {
    for (int j = 0; j < (int)b.v.size(); j++) {
      if (are_negations(a.v[i], b.v[i])) {
        vector<int> t;
        for (int k = 0; k < (int)a.v.size(); k++) {
          if (k != i) {
            t.push_back(a.v[k]);
          }
        }
        for (int k = 0; k < (int)b.v.size(); k++) {
          if (k != j) {
            t.push_back(b.v[k]);
          }
        }
        uint32_t mask = get_sort_uses_mask(t);
        add_checking_subsumes(make_entry(t,
            mask & (a.forall_mask | b.forall_mask),
            mask & (a.exists_mask | b.exists_mask)
           ));
      }
    }
  }
}

bool Flood::are_negations(int a, int b) {
  return negation_map[a] == b;
}

uint32_t Flood::get_sort_uses_mask(std::vector<int> const& t)
{
  uint32_t uses = 0;
  for (int x : t) {
    uses |= sort_uses_masks[x]; 
  }
  return uses;
}

bool Flood::in_bounds(Entry const& e)
{
  return (int)e.v.size() <= max_k
      && exists_count(e) <= max_e;
}

void Flood::process(Entry const& e)
{
  process_replace_forall_with_exists(e);
}

void Flood::process_replace_forall_with_exists(Entry const& e)
{
  for (int i = 0; i < nsorts; i++) {
    if ((e.forall_mask >> i) & 1) {
      Entry f;
      f.v = e.v;
      f.forall_mask = e.forall_mask & ~(1 << i);
      f.exists_mask = e.exists_mask | (1 << i);
      f.subsumed = false;
      add_checking_subsumes(f);
    }
  }
}

int Flood::exists_count(Entry const& e)
{
  uint64_t uses_mask = 0;
  for (int x : e.v) {
    uses_mask |= x;
  }
  uint64_t exists_mask = 0;
  for (int i = 0; i < nsorts; i++) {
    if ((e.exists_mask >> i) & 1) {
      exists_mask |= var_of_sort_masks[i];
    }
  }
  return __builtin_popcount(uses_mask & exists_mask);
}

void Flood::init_negation_map()
{
  int l = (int)enum_info.clauses.size();
  negation_map.resize(l);
  for (int i = 0; i < l; i++) {
    negation_map[i] = -1;
  }
  for (int i = 0; i < l; i++) {
    value v = enum_info.clauses[i];
    while (true) {
      if (Forall* f = dynamic_cast<Forall*>(v.get())) {
        v = f->body;
      }
      else if (Exists* f = dynamic_cast<Exists*>(v.get())) {
        v = f->body;
      }
      else {
        break;
      }
    }
    Not* no = dynamic_cast<Not*>(v.get());
    if (no != NULL) {
      int j = get_index_of_piece(no->val);
      if (j != -1) {
        negation_map[j] = i;
        negation_map[i] = j;
      }
    }
  }
}

struct IdenMask {
  uint32_t sort_use_mask;
  uint64_t var_use_mask;
};

void Flood::init_masks()
{
  this->var_of_sort_masks.resize(nsorts);
  for (int i = 0; i < nsorts; i++) {
    this->var_of_sort_masks[i] = 0;
  }

  map<iden, IdenMask> m;

  vector<Alternation> alts = forall_taqd.alternations();
  assert (alts.size() == 1);
  Alternation alt = alts[0];
  int v_idx = 0;
  for (int i = 0; i < (int)module->sorts.size(); i++) {
    lsort so = s_uninterp(module->sorts[i]);
    for (VarDecl const& decl : alt.decls) {
      if (sorts_eq(decl.sort, so)) {
        IdenMask im;
        assert(i < 8 * (int)sizeof(im.sort_use_mask));
        im.sort_use_mask = (1 << i);

        assert(v_idx < 8 * (int)sizeof(im.var_use_mask));
        im.var_use_mask = (1 << v_idx);

        m.insert(make_pair(decl.name, im));

        this->var_of_sort_masks[i] |= (1 << v_idx);

        v_idx++;
      }
    }
  }

  int l = (int)enum_info.clauses.size();

  sort_uses_masks.resize(l);
  var_uses_masks.resize(l);

  for (int i = 0; i < l; i++) {
    set<iden> used_vars;
    enum_info.clauses[i]->get_used_vars(used_vars /* output */);

    uint32_t sort_use_mask = 0;
    uint64_t var_use_mask = 0;
    for (iden id : used_vars) {
      auto it = m.find(id);
      assert(it != m.end());
      sort_use_mask |= it->second.sort_use_mask;
      var_use_mask |= it->second.var_use_mask;
    }
    this->sort_uses_masks[i] = sort_use_mask;
    this->var_uses_masks[i] = var_use_mask;
  }
}
