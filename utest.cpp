#define BOOST_TEST_MODULE party

#include <chrono>
#include <iostream>
#include <set>

#include <boost/test/unit_test.hpp>

#include "party.hpp"


using clock_type = std::chrono::system_clock;
using namespace party;


BOOST_AUTO_TEST_SUITE(functional_tests)


// functions should work for any movable element type
// including non-comparable and non-copyable types

struct element {
	element(element&& other) = default;
	element& operator = (element&& other) = default;
	element(size_t value = 0) : value(value) {}
	operator int () const {return value;}
	size_t value;
};


BOOST_AUTO_TEST_CASE(seventh_bell_number) {
	std::cout << "Constructing unordered partitions" << std::endl;
	std::vector<size_t> elements {1,2,3,4,5,6,7};

	size_t counter = 0;

	// set up generation for elements on non-copyable type
	auto root = first_set_partition<element>(elements);
	auto start = clock_type::now();
	for(bool is_valid(1); is_valid; is_valid = next_unordered_partition(root)) {
//		std::cout << counter << ":\t" << root << std::endl;
		++counter;
	}

	std::cout << counter << " partitions generated" << std::endl;
	BOOST_CHECK_EQUAL(counter, 877);

	root = last_set_partition<element>(elements);

	for(bool is_valid(1); is_valid; is_valid = prev_unordered_partition(root)) {
//		std::cout << counter << ":\t" << root << std::endl;
		--counter;
	}

	std::cout << counter << " partitions left after reverse" << std::endl;
	BOOST_CHECK_EQUAL(counter, 0);

	auto finish = clock_type::now();
	auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(finish - start).count();
	std::cout << elapsed << " milliseconds elapsed" << std::endl;
}


BOOST_AUTO_TEST_CASE(fifth_ordered_bell_number) {
	std::cout << "Constructing ordered paritions" << std::endl;
	std::vector<size_t> elements {1,2,3,4,5};

	auto start = clock_type::now();
	size_t counter = 0;

	// set up generation for elements on non-copyable type
	auto root = first_set_partition<element>(elements);
	for(bool is_valid(1); is_valid; is_valid = next_ordered_partition(root)) {
//		std::cout << ++counter << ":\t" << root << std::endl;
		++counter;
	}

	std::cout << counter << " partitions constructed" << std::endl;
	BOOST_CHECK_EQUAL(counter, 541);

	root = last_set_partition<element>(elements);
	for(bool is_valid(1); is_valid; is_valid = prev_ordered_partition(root)) {
//		std::cout << --counter << ":\t" << root << std::endl;
		--counter;
	}

	std::cout << counter << " partitions left after reverse" << std::endl;
	BOOST_CHECK_EQUAL(counter, 0);

	auto finish = clock_type::now();
	auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(finish - start).count();
	std::cout << elapsed << " milliseconds elapsed" << std::endl;
}


BOOST_AUTO_TEST_CASE(Ono_and_Nakano_extension) {
	std::vector<size_t> elements {1,2,3,4,5,6};
	std::vector<extension<size_t>> exhaustive, forward, reverse;
	std::set<std::pair<size_t, size_t>> relation {
		{1,2}, {1,4}, {2,4}, {3,5}, {3,6}, {5,6}
	};

	// find extensions with exhaustive search
	auto use_exhaustive_search = [&] () {
		extension<size_t> root;
		root.elements = elements;
		root.index.resize(elements.size());
		std::iota(root.index.begin(), root.index.end(), 0);
		while (true) {

			auto e_begin = root.elements.begin(), e_end = root.elements.end();
			auto r_iter = relation.begin(), r_end = relation.end();
			for(; r_iter != r_end; ++r_iter) {

				// find positions of the elements spesified by the relation
				size_t source = std::distance(e_begin, std::find(e_begin, e_end, r_iter->first));
				size_t target = std::distance(e_begin, std::find(e_begin, e_end, r_iter->second));

				// check relation requirements
				if (source > target) break;
			}

			if (r_iter == r_end) exhaustive.emplace_back(root);
			if (!std::next_permutation(root.index.begin(), root.index.end())) break;
			for(size_t i = 0; i < root.index.size(); ++i) {
				root.elements[i] = elements[root.index[i]];
			}
		}
	};

	// find extensions with forward enumeration algorithm
	auto use_forward_enumeration = [&] () {
		auto ps = make_poset<size_t>(elements, relation);
		auto root = first_poset_extension(ps);

		do forward.push_back(root);
		while (next_poset_extension(root, ps));
	};

	// find extensions with reverse enumeration algorithm
	auto use_reverse_enumeration = [&] () {
		auto ps = make_poset<size_t>(elements, relation);
		auto root = last_poset_extension(ps);

		do reverse.push_back(root);
		while (prev_poset_extension(root, ps));
	};

	use_exhaustive_search();
	use_forward_enumeration();
	use_reverse_enumeration();

	std::cout << "exhaustive search : " << exhaustive.size() << std::endl;
	std::cout << "forward enumeration : " << forward.size() << std::endl;
	std::cout << "reverse enumeration : " << reverse.size() << std::endl;

	BOOST_CHECK(exhaustive.size() == forward.size());
	BOOST_CHECK(exhaustive.size() == reverse.size());

//	std::reverse(forward.begin(), forward.end());
//	BOOST_CHECK(forward == reverse);
}


BOOST_AUTO_TEST_CASE(opartition_example_by_Ono_and_Nakano) {
	std::vector<size_t> elements {1,2,3,4,5,6};
	std::vector<partition<size_t>> exhaustive, forward, reverse;
	std::set<std::pair<size_t, size_t>> relation {
		{1,2}, {1,4}, {2,4}, {3,5}, {3,6}, {5,6}
	};

	// find partitions using exhaustive search
	auto use_exhaustive_search = [&] () {
		auto root = first_set_partition<size_t>(elements);		
		while (true) {

			auto e_begin = root.elements.begin(), e_end = root.elements.end();
			auto r_iter = relation.begin(), r_end = relation.end();
			for(; r_iter != r_end; ++r_iter) {

				// find positions of the elements spesified by the relation
				size_t source = std::distance(e_begin, std::find(e_begin, e_end, r_iter->first));
				size_t target = std::distance(e_begin, std::find(e_begin, e_end, r_iter->second));

				// check relation requirements
				if (source > target) break;

				// items should belong to different segments
				auto s_begin = root.segments.begin();
				auto s_min = s_begin + std::min(source, target);
				auto s_max = s_begin + std::max(source, target);
				while (s_max != s_min && !*s_max) --s_max;
				if (s_max == s_min) break;
			}

			if (r_iter == r_end) exhaustive.emplace_back(root);
			if (!next_ordered_partition(root)) break;
		}
	};

	// find partitions with forward enumeration algorithm
	auto use_forward_enumeration = [&] () {
		auto ps = make_poset<size_t>(elements, relation);
		auto root = first_poset_partition(ps);

		do forward.push_back(root);
		while (next_poset_partition(root, ps));
	};

	// find partitions with reverse enumeration algorithm
	auto use_reverse_enumeration = [&] () {
		auto ps = make_poset<size_t>(elements, relation);
		auto root = last_poset_partition(ps);

		do reverse.push_back(root);
		while (prev_poset_partition(root, ps));
	};

	use_exhaustive_search();
	use_forward_enumeration();
	use_reverse_enumeration();

	std::cout << "exhaustive search : " << exhaustive.size() << std::endl;
	std::cout << "forward enumeration : " << forward.size() << std::endl;
	std::cout << "reverse enumeration : " << reverse.size() << std::endl;

	BOOST_CHECK(exhaustive.size() == forward.size());
	BOOST_CHECK(exhaustive.size() == reverse.size());

//	std::reverse(forward.begin(), forward.end());
//	BOOST_CHECK(forward == reverse);
}


BOOST_AUTO_TEST_SUITE_END()
