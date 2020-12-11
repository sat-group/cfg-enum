#ifndef CEX_PRIORITY_H
#define CEX_PRIORITY_H

struct PEntry {
  //int sz;
  int next;
  int prev;
};

struct Prioritizer {
private:
  std::vector<PEntry> l;
  int head;
  int tail;

  void ll_append_front(PEntry pe);
  void ll_move_to_front(int i);

public:

  Prioritizer() {
    head = -1;
    tail = -1;
  }

  void append(int sz);
  int begin();
  int next(int cur);

  void record_hit(int i);
  void record_miss(int i) { }
};

inline void Prioritizer::append(int sz)
{
  PEntry pe;
  //pe.sz = sz;

  ll_append_front(pe);
}

inline int Prioritizer::begin()
{
  return this->head;
}

inline int Prioritizer::next(int cur)
{
  return this->l[cur].next;
}

inline void Prioritizer::record_hit(int i)
{
  ll_move_to_front(i);
}

inline void Prioritizer::ll_append_front(PEntry pe)
{
  pe.prev = -1;
  pe.next = this->head;
  l.push_back(pe);

  if (this->head != -1) {
    l[this->head].prev = l.size() - 1;
  } else {
    this->tail = l.size() - 1;
  }
  this->head = l.size() - 1;
}

inline void Prioritizer::ll_move_to_front(int i)
{
  int prev = l[i].prev;
  int next = l[i].next;
  if (prev == -1) {
    return;
  }

  l[prev].next = next;
  if (next == -1) {
    tail = prev;
  } else {
    l[next].prev = prev;
  }

  int orig_head = this->head;

  l[orig_head].prev = i;
  l[i].prev = -1;
  l[i].next = orig_head;
  this->head = i; 
}

#endif
