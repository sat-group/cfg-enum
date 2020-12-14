#ifndef BITSET_EVAL_RESULT_H
#define BITSET_EVAL_RESULT_H

#include <iostream>
#include <cstring>
#include <cassert>

//#define BIT_SANITY_CHECK

struct BitsetEvalResult {
  std::vector<uint64_t> v;
  uint64_t last_bits;

  static BitsetEvalResult eval_over_foralls(std::shared_ptr<Model>, value v);

  static BitsetEvalResult eval_over_alternating_quantifiers(std::shared_ptr<Model>, value v);

  static bool disj_is_true(std::vector<BitsetEvalResult*> const& results) {
    int n = results[0]->v.size();
    for (int i = 0; i < n - 1; i++) {
      uint64_t x = 0;
      for (int j = 0; j < (int)results.size(); j++) {
        x |= results[j]->v[i];
      }
      if (x != ~(uint64_t)0) {
        return false;
      }
    }

    uint64_t x = 0;
    for (int j = 0; j < (int)results.size(); j++) {
      x |= results[j]->v[n-1];
    }
    if (x != results[0]->last_bits) {
      return false;
    }

    return true;
  }

  void apply_disj(BitsetEvalResult const& ber) {
    for (int i = 0; i < (int)v.size(); i++) {
      v[i] |= ber.v[i];
    }
  }

  void apply_conj(BitsetEvalResult const& ber) {
    for (int i = 0; i < (int)v.size(); i++) {
      v[i] &= ber.v[i];
    }
  }

  void dump() {
    for (int i = 0; i < (int)v.size(); i++) {
      for (int j = 0; j < 64; j++) {
        if (i < (int)v.size() - 1 || (((uint64_t)1 << j) & last_bits)) {
          std::cout << (v[i] & ((uint64_t)1 << j) ? 1 : 0);
        }
      }
    }
    std::cout << std::endl;
  }
};

struct BitsetLevel {
  int block_size;
  int num_blocks;
  bool conj;
};

struct EasyLevel {
  int shift;
  bool conj;
};

inline void print_bits64(uint64_t t) {
  for (int i = 0; i < 64; i++) {
    int b = (int)((t >> i) & 1);
    std::cout << b;
  }
  std::cout << std::endl;
}

struct AlternationBitsetEvaluator {
  std::vector<uint64_t> scratch;

  std::vector<BitsetLevel> levels;

  bool collapse_pass_conj;
  bool collapse_pass_disj;
  int collapse_pass_left_shift_amt;
  int collapse_pass_final_idx;
  int collapse_pass_target;
  uint64_t collapse_pass_final_mask;
  int collapse_final_shift_amt;

  bool use_easy_levels;
  std::vector<EasyLevel> easy_levels;

  bool final_conj;
  int final_num_full_words_64;
  uint64_t final_last_bits;

  static AlternationBitsetEvaluator make_evaluator(
      std::shared_ptr<Model> model, value v);

  void dump(int k) {
    for (int i = 0; i < k; i++) {
      int b = (int)((scratch[i / 64] >> (i % 64)) & 1);
      std::cout << b;
    }
    std::cout << std::endl;
  }

  void reset_for_conj() {
    for (int i = 0; i < (int)scratch.size(); i++) {
      scratch[i] = ~(uint64_t)0;
    }
  }
  void reset_for_disj() {
    for (int i = 0; i < (int)scratch.size(); i++) {
      scratch[i] = 0;
    }
  }

  void add_conj(BitsetEvalResult const& ber) {
    for (int i = 0; i < (int)ber.v.size(); i++) {
      scratch[i] &= ber.v[i];
    }
  }
  void add_disj(BitsetEvalResult const& ber) {
    for (int i = 0; i < (int)ber.v.size(); i++) {
      scratch[i] |= ber.v[i];
    }
  }

  void add_conj(int sz, std::vector<uint64_t> const& v) {
    for (int i = 0; i < sz; i++) {
      scratch[i] &= v[i];
    }
  }
  void add_disj(int sz, std::vector<uint64_t> const& v) {
    for (int i = 0; i < sz; i++) {
      scratch[i] |= v[i];
    }
  }

  static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__, "this requires little endian");

  // scratch[0 .. len] := scratch[0 .. len] & scratch[start .. start + len]
  void block_conj(int start, int len) {
    // word of 4 bytes at a time
    int t;
    for (t = 0; 32*t <= len - 32; t++) {
      int bit_idx = 32*t + start;
      int w32_idx = bit_idx / 32;
      uint64_t w64;
      memcpy(&w64, ((uint32_t*)&scratch[0]) + w32_idx, 8);
      uint32_t block = (uint32_t)(w64 >> ((start % 32)));

      uint32_t tmp;
      memcpy(&tmp, ((uint32_t*)&scratch[0]) + t, 4);
      tmp &= block;
      memcpy(((uint32_t*)&scratch[0]) + t, &tmp, 4);
    }

    if (32*t < len) {
      int bit_idx = 32*t + start;
      int w32_idx = bit_idx / 32;
      uint64_t w64;
      memcpy(&w64, ((uint32_t*)&scratch[0]) + w32_idx, 8);
      uint32_t block = (uint32_t)(w64 >> ((start % 32)));

      uint32_t tmp;
      memcpy(&tmp, ((uint32_t*)&scratch[0]) + t, 4);
      tmp &= block | ((uint32_t)(-1) << (len - 32*t));
      memcpy(((uint32_t*)&scratch[0]) + t, &tmp, 4);
    }
  }

  // scratch[0 .. len] := scratch[0 .. len] | scratch[start .. start + len]
  void block_disj(int start, int len) {
    int t;
    for (t = 0; 32*t <= len - 32; t++) {
      int bit_idx = 32*t + start;
      int w32_idx = bit_idx / 32;
      uint64_t w64;
      memcpy(&w64, ((uint32_t*)&scratch[0]) + w32_idx, 8);
      uint32_t block = (uint32_t)(w64 >> ((start % 32)));

      uint32_t tmp;
      memcpy(&tmp, ((uint32_t*)&scratch[0]) + t, 4);
      tmp |= block;
      memcpy(((uint32_t*)&scratch[0]) + t, &tmp, 4);
    }

    if (32*t < len) {
      int bit_idx = 32*t + start;
      int w32_idx = bit_idx / 32;
      uint64_t w64;
      memcpy(&w64, ((uint32_t*)&scratch[0]) + w32_idx, 8);
      uint32_t block = (uint32_t)(w64 >> ((start % 32)));

      uint32_t tmp;
      memcpy(&tmp, ((uint32_t*)&scratch[0]) + t, 4);
      tmp |= block & (((uint32_t)(1) << (len - 32*t)) - 1);
      memcpy(((uint32_t*)&scratch[0]) + t, &tmp, 4);
    }
  }

  bool final_answer() {
    if (final_conj) {
      for (int j = 0; j < final_num_full_words_64; j++) {
        if (scratch[j] != ~(uint64_t)0) {
          return false;
        }
      }
      return (scratch[final_num_full_words_64] & final_last_bits)
          == final_last_bits;
    } else {
      for (int j = 0; j < final_num_full_words_64; j++) {
        if (scratch[j] != 0) {
          return true;
        }
      }
      return (scratch[final_num_full_words_64] & final_last_bits) != 0;
    }
  }

  bool final_answer(uint64_t final) {
    if (final_conj) {
      return (final & final_last_bits)
          == final_last_bits;
    } else {
      //std::cout << "final_answer: !final_conj" << std::endl;
      //std::cout << final << std::endl;
      //std::cout << final_last_bits << std::endl;
      return (final & final_last_bits) != 0;
    }
  }

  bool evaluate() {
    for (int i = 0; i < (int)levels.size(); i++) {
      BitsetLevel& level = levels[i];
      if (level.conj) {
        for (int j = 1; j < level.num_blocks; j++) {
          block_conj(j * level.block_size, level.block_size);
        }
      } else {
        for (int j = 1; j < level.num_blocks; j++) {
          block_disj(j * level.block_size, level.block_size);
        }
      }
    }

    uint64_t word;

    if (collapse_pass_conj) {
      //std::cout << "collapse_pass_conj" << std::endl;
      //dump(228);

      word = ~scratch[0];
      //std::cout << "word: "; print_bits64(word);
      int shift = collapse_pass_left_shift_amt;
      int target = collapse_pass_target;
      for (int i = 1; i < collapse_pass_final_idx; i++) {
        uint64_t w = ~scratch[i];
        word = word
          | (w << shift)
          | (w >> (target - shift));

        //std::cout << "shift: " << shift << std::endl;
        shift = (shift + collapse_pass_left_shift_amt);
        if (shift > target) {
          shift -= target;
        }
        //std::cout << "w:    "; print_bits64(w);
        //std::cout << "word: "; print_bits64(word);
      }
      uint64_t w = (~scratch[collapse_pass_final_idx]) & collapse_pass_final_mask;
      word = word
        | (w << shift)
        | (w >> (target - shift));
      //std::cout << "w:    "; print_bits64(w);
      //std::cout << "word: "; print_bits64(word);
      word = word | (word >> collapse_final_shift_amt);
      word = ~word;

      //print_bits64(word);

      goto use_easy_levels_lbl;
    } else if (collapse_pass_disj) {
      //std::cout << "collapse_pass_disj" << std::endl;
      //dump(90);

      word = scratch[0];
      //print_bits64(word);
      int shift = collapse_pass_left_shift_amt;
      int target = collapse_pass_target;
      for (int i = 1; i < collapse_pass_final_idx; i++) {
        uint64_t w = scratch[i];
        word = word
          | (w << shift)
          | (w >> (target - shift));

        //std::cout << "shift: " << shift << std::endl;
        shift = (shift + collapse_pass_left_shift_amt);
        if (shift > target) {
          shift -= target;
        }
        //std::cout << "w:    "; print_bits64(w);
        //std::cout << "word: "; print_bits64(word);
      }
      uint64_t w = scratch[collapse_pass_final_idx] & collapse_pass_final_mask;
      word = word
        | (w << shift)
        | (w >> (target - shift));
      //std::cout << "w:    "; print_bits64(w);
      //std::cout << "word: "; print_bits64(word);
      word = word | (word >> collapse_final_shift_amt);
      //std::cout << "collapse_final_shift_amt " << collapse_final_shift_amt << std::endl;
      //std::cout << "word: "; print_bits64(word);

      //print_bits64(word);

      goto use_easy_levels_lbl;
    }

    if (use_easy_levels) {
      //std::cout << "use_easy_levels" << std::endl;
      word = scratch[0];
      //print_bits64(word);

      use_easy_levels_lbl:

      for (int i = 0; i < (int)easy_levels.size(); i++) {
        EasyLevel& level = easy_levels[i];
        //std::cout << "level " << level.conj << " " << level.shift << std::endl;
        if (level.conj) {
          word = word & (word >> level.shift);
        } else {
          word = word | (word >> level.shift);
        }
        //std::cout << "i = " << i << std::endl;
        //print_bits64(word);
      }

      //print_bits64(word);
      //print_bits64(final_last_bits);
      //std::cout << final_conj << std::endl;
      return final_answer(word);
    }

    bool res = final_answer();
    return res;
  }
};

inline void vec_copy_ber(std::vector<uint64_t>& v, BitsetEvalResult const& ber) {
  for (int i = 0; i < (int)ber.v.size(); i++) {
    v[i] = ber.v[i];
  }
}

inline void vec_apply_disj(std::vector<uint64_t>& v, BitsetEvalResult const& ber) {
  for (int i = 0; i < (int)ber.v.size(); i++) {
    v[i] |= ber.v[i];
  }
}

inline void vec_apply_conj(std::vector<uint64_t>& v, BitsetEvalResult const& ber) {
  for (int i = 0; i < (int)ber.v.size(); i++) {
    v[i] &= ber.v[i];
  }
}


#endif
