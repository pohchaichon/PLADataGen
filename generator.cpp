#include <iostream>
#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <iterator>
#include <limits>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <vector>
#include <fstream>
#include <stdlib.h>
#include <random>
#include <cmath>
#include <cstring>

template<typename T>
using LargeSigned = typename std::conditional_t<std::is_floating_point_v<T>,
                                                long double,
                                                std::conditional_t<(sizeof(T) < 8), int64_t, __int128>>;

template<typename X, typename Y>
class OptimalPiecewiseLinearModel {
private:
    using SX = LargeSigned<X>;
    using SY = LargeSigned<Y>;

    struct Slope {
        SX dx{};
        SY dy{};

        bool operator<(const Slope &p) const { return dy * p.dx < dx * p.dy; }
        bool operator>(const Slope &p) const { return dy * p.dx > dx * p.dy; }
        bool operator==(const Slope &p) const { return dy * p.dx == dx * p.dy; }
        bool operator!=(const Slope &p) const { return dy * p.dx != dx * p.dy; }
        explicit operator long double() const { return dy / (long double) dx; }
    };

    struct Point {
        X x{};
        Y y{};

        Slope operator-(const Point &p) const { return {SX(x) - p.x, SY(y) - p.y}; }
    };

    const Y epsilon;
    std::vector<Point> lower;
    std::vector<Point> upper;
    X first_x = 0;
    X last_x = 0;
    size_t lower_start = 0;
    size_t upper_start = 0;
    size_t points_in_hull = 0;
    Point rectangle[4];

    auto cross(const Point &O, const Point &A, const Point &B) const {
        auto OA = A - O;
        auto OB = B - O;
        return OA.dx * OB.dy - OA.dy * OB.dx;
    }

public:

    class CanonicalSegment;

    explicit OptimalPiecewiseLinearModel(Y epsilon) : epsilon(epsilon), lower(), upper() {
        if (epsilon < 0)
            throw std::invalid_argument("epsilon cannot be negative");

        upper.reserve(1u << 16);
        lower.reserve(1u << 16);
    }

    bool check_point(const X &x, const Y &y) {
        if (points_in_hull > 0 && x <= last_x)
            throw std::logic_error("CHECK: Points must be increasing by x.");

        last_x = x;
        auto max_y = std::numeric_limits<Y>::max();
        auto min_y = std::numeric_limits<Y>::lowest();
        Point p1{x, y >= max_y - epsilon ? max_y : y + epsilon};
        Point p2{x, y <= min_y + epsilon ? min_y : y - epsilon};

        if (points_in_hull == 0) {
            return true;
        }

        if (points_in_hull == 1) {
            return true;
        }

        auto slope1 = rectangle[2] - rectangle[0];
        auto slope2 = rectangle[3] - rectangle[1];
        bool outside_line1 = p1 - rectangle[2] < slope1;
        bool outside_line2 = p2 - rectangle[3] > slope2;

        if (outside_line1 || outside_line2) {
            points_in_hull = 0;
            return false;
        } else return true;
    }

    bool add_point(const X &x, const Y &y) {
        if (points_in_hull > 0 && x <= last_x)
            throw std::logic_error("ADD: Points must be increasing by x.");

        last_x = x;
        auto max_y = std::numeric_limits<Y>::max();
        auto min_y = std::numeric_limits<Y>::lowest();
        Point p1{x, y >= max_y - epsilon ? max_y : y + epsilon};
        Point p2{x, y <= min_y + epsilon ? min_y : y - epsilon};

        if (points_in_hull == 0) {
            first_x = x;
            rectangle[0] = p1;
            rectangle[1] = p2;
            upper.clear();
            lower.clear();
            upper.push_back(p1);
            lower.push_back(p2);
            upper_start = lower_start = 0;
            ++points_in_hull;
            return true;
        }

        if (points_in_hull == 1) {
            rectangle[2] = p2;
            rectangle[3] = p1;
            upper.push_back(p1);
            lower.push_back(p2);
            ++points_in_hull;
            return true;
        }

        auto slope1 = rectangle[2] - rectangle[0];
        auto slope2 = rectangle[3] - rectangle[1];
        bool outside_line1 = p1 - rectangle[2] < slope1;
        bool outside_line2 = p2 - rectangle[3] > slope2;

        if (outside_line1 || outside_line2) {
            points_in_hull = 0;
            return false;
        }

        if (p1 - rectangle[1] < slope2) {
            // Find extreme slope
            auto min = lower[lower_start] - p1;
            auto min_i = lower_start;
            for (auto i = lower_start + 1; i < lower.size(); i++) {
                auto val = lower[i] - p1;
                if (val > min)
                    break;
                min = val;
                min_i = i;
            }

            rectangle[1] = lower[min_i];
            rectangle[3] = p1;
            lower_start = min_i;

            // Hull update
            auto end = upper.size();
            for (; end >= upper_start + 2 && cross(upper[end - 2], upper[end - 1], p1) <= 0; --end)
                continue;
            upper.resize(end);
            upper.push_back(p1);
        }

        if (p2 - rectangle[0] > slope1) {
            // Find extreme slope
            auto max = upper[upper_start] - p2;
            auto max_i = upper_start;
            for (auto i = upper_start + 1; i < upper.size(); i++) {
                auto val = upper[i] - p2;
                if (val < max)
                    break;
                max = val;
                max_i = i;
            }

            rectangle[0] = upper[max_i];
            rectangle[2] = p2;
            upper_start = max_i;

            // Hull update
            auto end = lower.size();
            for (; end >= lower_start + 2 && cross(lower[end - 2], lower[end - 1], p2) >= 0; --end)
                continue;
            lower.resize(end);
            lower.push_back(p2);
        }

        ++points_in_hull;
        return true;
    }

    CanonicalSegment get_segment() {
        if (points_in_hull == 1)
            return CanonicalSegment(rectangle[0], rectangle[1], first_x);
        return CanonicalSegment(rectangle, first_x);
    }

    void reset() {
        points_in_hull = 0;
        lower.clear();
        upper.clear();
    }
};

template<typename X, typename Y>
class OptimalPiecewiseLinearModel<X, Y>::CanonicalSegment {
    friend class OptimalPiecewiseLinearModel;

    Point rectangle[4];
    X first;

    CanonicalSegment(const Point &p0, const Point &p1, X first) : rectangle{p0, p1, p0, p1}, first(first) {};

    CanonicalSegment(const Point (&rectangle)[4], X first)
        : rectangle{rectangle[0], rectangle[1], rectangle[2], rectangle[3]}, first(first) {};

    bool one_point() const {
        return rectangle[0].x == rectangle[2].x && rectangle[0].y == rectangle[2].y
            && rectangle[1].x == rectangle[3].x && rectangle[1].y == rectangle[3].y;
    }

public:

    CanonicalSegment() = default;

    X get_first_x() const { return first; }

    std::pair<long double, long double> get_intersection() const {
        auto &p0 = rectangle[0];
        auto &p1 = rectangle[1];
        auto &p2 = rectangle[2];
        auto &p3 = rectangle[3];
        auto slope1 = p2 - p0;
        auto slope2 = p3 - p1;

        if (one_point() || slope1 == slope2)
            return {p0.x, p0.y};

        auto p0p1 = p1 - p0;
        auto a = slope1.dx * slope2.dy - slope1.dy * slope2.dx;
        auto b = (p0p1.dx * slope2.dy - p0p1.dy * slope2.dx) / static_cast<long double>(a);
        auto i_x = p0.x + b * slope1.dx;
        auto i_y = p0.y + b * slope1.dy;
        return {i_x, i_y};
    }

    std::pair<long double, SY> get_floating_point_segment(const X &origin) const {
        if (one_point())
            return {0, (rectangle[0].y + rectangle[1].y) / 2};

        if constexpr (std::is_integral_v<X> && std::is_integral_v<Y>) {
            auto slope = rectangle[3] - rectangle[1];
            auto intercept_n = slope.dy * (SX(origin) - rectangle[1].x);
            auto intercept_d = slope.dx;
            auto rounding_term = ((intercept_n < 0) ^ (intercept_d < 0) ? -1 : +1) * intercept_d / 2;
            auto intercept = (intercept_n + rounding_term) / intercept_d + rectangle[1].y;
            return {static_cast<long double>(slope), intercept};
        }

        auto[i_x, i_y] = get_intersection();
        auto[min_slope, max_slope] = get_slope_range();
        auto slope = (min_slope + max_slope) / 2.;
        auto intercept = i_y - (i_x - origin) * slope;
        return {slope, intercept};
    }

    std::pair<long double, long double> get_slope_range() const {
        if (one_point())
            return {0, 1};

        auto min_slope = static_cast<long double>(rectangle[2] - rectangle[0]);
        auto max_slope = static_cast<long double>(rectangle[3] - rectangle[1]);
        return {min_slope, max_slope};
    }
};

template<typename KEY_TYPE>
size_t PGM_metric(KEY_TYPE *keys, int key_num, int error_bound) {
    OptimalPiecewiseLinearModel<KEY_TYPE, uint64_t> segment(error_bound);
    std::sort(keys, keys+key_num);
    size_t metric = 1;
    double max = 0;
    for(auto i = 0; i < key_num; i++) {
        if(!segment.add_point(keys[i], i)) {
            metric++;
            segment.reset();
            segment.add_point(keys[i], i);
        }
    }
    return metric;
}

void dataGenerator(int local_epsilon, int global_epsilon, int local_value, int global_value, int num, std::string out_path) {
    std::cout << "local epsilon: " << local_epsilon << std::endl;
    std::cout << "global epsilon: " << global_epsilon << std::endl;
    std::cout << "local value: " << local_value << std::endl;
    std::cout << "global value: " << global_value << std::endl;

    uint64_t *data = new uint64_t[num+1];
    data[0] = num;
    OptimalPiecewiseLinearModel<uint64_t, uint64_t> local_pla(local_epsilon);
    OptimalPiecewiseLinearModel<uint64_t, uint64_t> global_pla(global_epsilon);
    local_pla.reset();
    global_pla.reset();

    // local pass
    std::cout << "--- local pass ---" << std::endl;
    int key_per_model = num / local_value;
    uint64_t curr_rank = 1;
    uint64_t curr_key = 0;
    for(int i = 0; i < local_value; i++) {
        std::cout << "\r" << i+1 << "/" << local_value << std::flush;
        int j;
        // increasing key
        for(j = 1; j <= key_per_model; j++) {
            data[curr_rank++] = curr_key;
            local_pla.add_point(curr_key, j);
            curr_key++;
        }
        // now find the 'out of bound' key
        while(local_pla.check_point(curr_key++, j));
        local_pla.reset();
    }
    // naive extend left over
    if(num % local_value != 0) {
        for(; curr_rank <= num+1; curr_rank++) {
            data[curr_rank] = curr_key++;
        }
    }
    std::cout << std::endl;

    // global pass
    std::cout << "--- global pass ---" << std::endl;
    key_per_model = num / global_value;
    curr_rank = 1;
    uint64_t offset = 0;
    for(int i = 0; i < global_value; i++) {
        std::cout << "\r" << i+1 << "/" << global_value << std::flush;
        int j;
        // key from local
        for(j = 1; j <= key_per_model; j++) {
            curr_key = data[curr_rank++];
            if(!global_pla.add_point(curr_key, j)) {
                std::cout << "global failed to encapsulate local" << std::endl;
                return;
            }
        }
        // now find the 'out of bound' key
        while(global_pla.check_point(++curr_key, j)) {
            offset++;
        }
        for(int k = curr_rank; k < num+1; k++) data[k] += offset;
        global_pla.reset();
        offset = 0;
    }
    std::cout << std::endl;

    if (out_path.size() > 0) {
        std::fstream file(out_path, std::ios::out | std::ios::binary);
        if(!file.is_open()) std::cout << "cannot write file" << std::endl;
        file.write(reinterpret_cast<char *>(data), sizeof(uint64_t) * (num+1));
        file.close();
        std::cout << "file written to " << out_path << std::endl;
    }
}

int main(int argc, char **argv) {
    dataGenerator(strtol(argv[1], nullptr, 0), strtol(argv[2], nullptr, 0), strtol(argv[3], nullptr, 0), strtol(argv[4], nullptr, 0), strtol(argv[5], nullptr, 0), argv[8]);
    return 0;
}