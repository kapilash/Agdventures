#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <algorithm>
#include <ranges>
#include <cstdint>
#include <functional>

// Link to fasta file: https://www.ncbi.nlm.nih.gov/nuccore/NC_000913.3?report=fasta


// Simple FASTA reader — minimal, no error handling, assumes single sequence per file
class Fasta {
    std::string header;
    std::string sequence;
public:
    bool read(const std::string& filename) {
        std::ifstream file(filename);
        if (!file.is_open()) return false;

        std::string line;
        while (std::getline(file, line)) {
            if (line.empty()) continue;
            if (line[0] == '>') {
                header = line.substr(1);
            } else {
                sequence += line;
            }
        }
        return !sequence.empty();
    }

    const std::string& get_header() const { return header; }
    const std::string& get_sequence() const { return sequence; }
};

// A:+1, T:+1, G:-1, C:-1
int score_base(char c) {
    switch (c) {
        case 'A': case 'a': return  1;
        case 'T': case 't': return  1;
        case 'G': case 'g': return -1;
        case 'C': case 'c': return -1;
        default: return 0;
    }
}


// Kadane (sum only) — mirrors the Agda definition:
//
//   mss-f : Extendedℤ × Extendedℤ → Extendedℤ → Extendedℤ × Extendedℤ
//   mss-f (u , v) x = (u ↑ ((v +ₑ x) ↑ 0ₑ)) , ((v +ₑ x) ↑ 0ₑ)
//
//   kadane lst = proj₁ (foldl mss-f (0ₑ , 0ₑ) lst)


using State = std::pair<int64_t, int64_t>;  // (u, v) — (global max, local max)

auto mss_f(State acc, int x) -> State {
    auto [u, v] = acc;
    auto v_new = std::max<int64_t>(v + x, 0);
    auto u_new = std::max(u, v_new);
    return {u_new, v_new};
}

auto kadane(const auto& scores) -> int64_t {
    auto [u, v] = std::ranges::fold_left(scores, State{0, 0}, mss_f);
    return u;
}


// Kadane with region tracking — extends mss-f with positions

struct Region {
    int64_t max_sum;
    size_t start;
    size_t end;
};

struct RegionState {
    int64_t u;              // global max
    int64_t v;              // local max ending here
    size_t best_start;
    size_t best_end;
    size_t local_start;
    size_t i;               // current index
};

auto mss_f_region(RegionState s, int x) -> RegionState {
    auto v_new = std::max<int64_t>(s.v + x, 0);
    auto local_start = (s.v + x < 0) ? s.i + 1 : s.local_start;
    auto u_new = std::max(s.u, v_new);

    auto best_start = (v_new > s.u) ? s.local_start : s.best_start;
    auto best_end   = (v_new > s.u) ? s.i           : s.best_end;

    return {u_new, v_new, best_start, best_end, local_start, s.i + 1};
}

auto kadane_region(const auto& scores) -> Region {
    auto s = std::ranges::fold_left(
        scores,
        RegionState{0, 0, 0, 0, 0, 0},
        mss_f_region
    );
    return {s.u, s.best_start, s.best_end};
}

int main(int argc, char* argv[]) {
    if (argc < 2) {
        std::cerr << "Usage: " << argv[0] << " <file.fasta>" << std::endl;
        return 1;
    }

    Fasta fasta;
    if (!fasta.read(argv[1])) {
        std::cerr << "Failed to read FASTA file" << std::endl;
        return 1;
    }

    const std::string& seq = fasta.get_sequence();
    auto scores = seq | std::views::transform(score_base);

    auto max_sum = kadane(scores);
    auto region  = kadane_region(scores);

    std::cout << "Sequence: " << fasta.get_header() << std::endl;
    std::cout << "Length:   " << seq.size() << " bp" << std::endl;
    std::cout << std::endl;
    std::cout << "kadane (sum only): " << max_sum << std::endl;
    std::cout << std::endl;
    std::cout << "kadane_region (AT-rich region):" << std::endl;
    std::cout << "  Position: " << region.start + 1 << " - " << region.end + 1
              << " (" << region.end - region.start + 1 << " bp)" << std::endl;
    std::cout << "  Score:    " << region.max_sum << std::endl;
    std::cout << "  Preview:  " << seq.substr(region.start, std::min<size_t>(60, region.end - region.start + 1))
              << (region.end - region.start + 1 > 60 ? "..." : "") << std::endl;

    return 0;
}
