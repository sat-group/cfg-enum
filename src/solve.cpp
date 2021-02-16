#include "solve.h"

#include <iostream>
#include <cassert>
#include <sstream>

#include "stats.h"
#include "benchmarking.h"

using namespace std;

extern int numRetries;
extern int numTryHardFailures;

smt::context _z3_ctx_normal;
smt::context _z3_ctx_quick;
smt::context _cvc4_ctx_normal;
smt::context _cvc4_ctx_quick;

void context_reset() {
  _z3_ctx_normal = smt::context();
  _z3_ctx_quick = smt::context();
  _cvc4_ctx_normal = smt::context();
  _cvc4_ctx_quick = smt::context();
}

smt::context z3_ctx_normal() {
  if (!_z3_ctx_normal.p) {
    _z3_ctx_normal = smt::context(smt::Backend::z3);
    _z3_ctx_normal.set_timeout(45000);
  }
  return _z3_ctx_normal;
}

smt::context z3_ctx_quick() {
  if (!_z3_ctx_quick.p) {
    _z3_ctx_quick = smt::context(smt::Backend::z3);
    _z3_ctx_quick.set_timeout(15000);
  }
  return _z3_ctx_quick;
}

smt::context cvc4_ctx_normal() {
  if (!_cvc4_ctx_normal.p) {
    _cvc4_ctx_normal = smt::context(smt::Backend::cvc4);
    _cvc4_ctx_normal.set_timeout(45000);
  }
  return _cvc4_ctx_normal;
}

smt::context cvc4_ctx_quick() {
  if (!_cvc4_ctx_quick.p) {
    _cvc4_ctx_quick = smt::context(smt::Backend::cvc4);
    _cvc4_ctx_quick.set_timeout(15000);
  }
  return _cvc4_ctx_quick;
}

struct Entry {
  bool is_cvc4;
  bool sat;
  bool unsat;
  bool unknown;
  long long ms;

  Entry() : is_cvc4(false), sat(false), unsat(false), unknown(false), ms(0) { }
};

long long solver_ms;

int smt_id = 0;
string log_directory;

void write_smt_log(stringstream& smtlog_ss, vector<Entry> const& entries,
    string const& log_info)
{
  smt_id++;

  string idstr = to_string(smt_id);
  while (idstr.size() < 6) {
    idstr = "0" + idstr;
  }

  string filename = log_directory;
  assert (filename != "");
  if (filename[filename.size() - 1] != '/') {
    filename += '/';
  }

  filename += idstr + ".smt";

  ofstream myfile;
  myfile.open(filename);

  myfile << "; " << log_info << endl << endl;

  for (Entry const& entry : entries) {
    myfile << "; API ";
    if (entry.is_cvc4) {
      myfile << "CVC4-prerelease-1.8";
    } else {
      myfile << "Z3-4.8.9";
    }

    myfile << " , " << entry.ms << " ms , ";

    if (entry.sat) myfile << "Sat";
    else if (entry.unsat) myfile << "Unsat";
    else if (entry.unknown) myfile << "Unknown";
    else { assert(false); }
  }

  string s = smtlog_ss.str();
  myfile << endl << s << endl;
  myfile << "(check-sat)" << endl;

  myfile.close();
}

ContextSolverResult context_solve(
    std::string const& log_info,
    std::shared_ptr<Module> module,
    ModelType mt,
    Strictness st,
    value hint,
    std::function<
        std::vector<std::shared_ptr<ModelEmbedding>>(std::shared_ptr<BackgroundContext>)
      > f)
{
  auto t1 = now();

  int num_fails = 0; 

  stringstream smtlog_ss;
  vector<Entry> entries;

  while (true) {
    bool use_cvc4 = !(num_fails % 2 == 0);
    smt::context ctx = (!use_cvc4
        ? (st == Strictness::Quick ? z3_ctx_quick() : z3_ctx_normal())
        : (st == Strictness::Quick ? cvc4_ctx_quick() : cvc4_ctx_normal())
    );
    shared_ptr<BackgroundContext> bgc;
    bgc.reset(new BackgroundContext(ctx, module));
    vector<shared_ptr<ModelEmbedding>> es = f(bgc);

    bgc->solver.set_log_info(log_info);
    if (num_fails == 0) {
      bgc->solver.p->dump(smtlog_ss);
    }
    smt::SolverResult res = bgc->solver.check_result();

    Entry entry;
    entry.is_cvc4 = use_cvc4;
    entry.ms = solver_ms;
    if (res == smt::SolverResult::Unknown) entry.unknown = true;
    if (res == smt::SolverResult::Sat) entry.sat = true;
    if (res == smt::SolverResult::Unsat) entry.unsat = true;
    entries.push_back(entry);

    if (
         st == Strictness::Indef
      || st == Strictness::Quick
      || (st == Strictness::TryHard && (num_fails == 10 || res != smt::SolverResult::Unknown))
      || (st == Strictness::Strict && res != smt::SolverResult::Unknown)
    ) {
      auto t2 = now();
      long long ms = as_ms(t2 - t1);
      global_stats.add_total(ms);
      if (num_fails > 0) {
        smt::add_stat_smt_long(ms);
      }

      ContextSolverResult csr;
      csr.res = res;
      if (es.size() > 0) {
        if (res == smt::SolverResult::Sat) {
          if (mt == ModelType::Any) {
            for (int i = 0; i < (int)es.size(); i++) {
              csr.models.push_back(Model::extract_model_from_z3(
                  bgc->ctx, bgc->solver, module, *es[i]));
            }
            csr.models[0]->dump_sizes();
          } else {
            auto t1 = now();

            csr.models = Model::extract_minimal_models_from_z3(
                bgc->ctx, bgc->solver, module, es, hint);

            auto t2 = now();
            long long ms = as_ms(t2 - t1);
            global_stats.add_model_min(ms);
          }
        }
      }

      if (st == Strictness::TryHard && res == smt::SolverResult::Unknown) {
        cout << "TryHard failure" << endl;
        numTryHardFailures++;
      }

      write_smt_log(smtlog_ss, entries, log_info);

      return csr;
    }

    num_fails++;
    numRetries++;
    assert(num_fails < 20);
    cout << "failure encountered, retrying" << endl;
  }
}
