#pragma once

extern "C" {
#include "btor2parser/btor2parser.h"
}

#include "math.h"
#include "stdio.h"
#include <algorithm>
#include <iostream>
#include <unordered_map>
#include <unordered_set>
#include <vector>

enum Kind { bitvec_k=0, array_k=1, none_k=2};

struct Sort
{
  Sort() : k(none_k), w1(0), w2(0) {}
  Sort(size_t w) : k(bitvec_k), w1(w), w2(0) {}
  Sort(size_t w, size_t v) : k(array_k), w1(w), w2(v) {}
  Kind k;
  size_t w1;
  size_t w2;
};


namespace btor2verilog
{
  class Btor2Verilog
  {
  public:
    Btor2Verilog() { initialize(); }
    ~Btor2Verilog() {}

    bool parse(const char * filename);
    bool gen_verilog();
    std::string get_verilog() { return verilog_; }
    std::string error() { return err_; }

  protected:
    void initialize();
    bool combinational_assignment();
    std::string get_full_select(size_t width) const;

    std::vector<std::string> sort_assertions_assumes(const std::vector<std::string> &_a);
    std::vector<std::vector<std::string>> sort_assignment(
          const std::unordered_map<std::string, std::string> & _assigns_);
    std::vector<size_t> sort_input_output(std::unordered_set<size_t> &_a);

    std::string err_;
    std::string verilog_;

    Btor2LineIterator it_;
    Btor2Line * l_;
    Sort linesort_;
    size_t i_;
    int64_t idx_;
    bool negated_;
    std::string sym_;
    std::string assign_;

    std::unordered_map<size_t, Sort> sorts_;
    std::vector<std::string> args_;

    std::unordered_map<size_t, std::string> symbols_;
    std::unordered_set<size_t> inputs_;
    std::unordered_set<size_t> outputs_;
    std::vector<size_t> states_;
    std::vector<size_t> wires_;

    std::vector<std::string> constraints_;
    std::unordered_map<std::string, std::string> init_;
    std::vector<std::string> props_;

    std::unordered_map<std::string, std::string> state_updates_;
    std::unordered_map<std::string, std::string> wire_assigns_;

    std::unordered_map<std::string, std::tuple<std::string, std::string,
                                               std::string, size_t, size_t>>
        writes_;
    ///< maps the array symbol name to the tuple of write info: array, index,
    ///< element, index width, element width
  };
}
