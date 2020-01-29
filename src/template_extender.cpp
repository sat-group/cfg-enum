#include "template_extender.h"

using namespace std;

value extend_template(shared_ptr<Module> module, value templ, int n)
{
  auto values = cached_get_unfiltered_values(module, 1);
  values->init_simp();
  vector<value> pieces = values->values;

  map<string, int> sort_to_count;

  for (string so : module->sorts) {
    int m = 0;
    for (value p : pieces) {
      m = max(m, count_sort_usage(p, so));
    }
    sort_to_count[so] = n*m;
  }
}
