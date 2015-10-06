#pragma once

#include <algorithm>
#include <cassert>
#include <deque>
#include <iostream>
#include <iterator>
#include <map>
#include <ostream>
#include <vector>
#include <unordered_set>


namespace party {

	template<typename Item>
	struct extension {
		using Elements = std::vector<Item>;
		using Index = std::vector<size_t>;

		Elements elements;
		Index index;
	};


	template<typename Item>
	struct poset {
		using Relation = std::set<std::pair<size_t, size_t>>;
		using Extension = extension<Item>;

		Relation relation;
		Extension ext;
	};


	template<typename Item>
	struct partition : public extension<Item> {
		using Elements = typename extension<Item>::Elements;
		using Index = typename extension<Item>::Index;
		using Segments = std::vector<size_t>;

		Segments segments;
	};

} // partition_lib


template<typename Item>
std::ostream& operator << (std::ostream &stream, const party::extension<Item>& x) {
	if (x.elements.empty()) return stream;
	auto iter = x.elements.cbegin();
	auto it_end = std::prev(x.elements.end());
	while (iter != it_end) stream << *iter++ << "<";
	return stream << *iter;
}


template<typename Item> std::ostream& operator <<
(std::ostream &stream, const party::partition<Item> &x) {
	auto e_iter = x.elements.cbegin();
	auto s_iter = x.segments.cbegin();
	while (s_iter != x.segments.end()) {
		stream << '{' << *e_iter++;
		auto it_end = s_iter + *s_iter;
		while (++s_iter != it_end)
			stream << ',' << *e_iter++;
		stream << '}';
	}
	return stream;
}


namespace party {

	template<typename Item, typename Container>
	partition<Item> first_set_partition(Container&& container) {
		partition<Item> root;
		root.elements.resize(container.size());
		root.segments.resize(container.size());
		root.index.resize(root.elements.size());
		std::iota(root.index.begin(), root.index.end(), 0);
		std::copy(std::begin(container), std::end(container), root.elements.begin());
		std::fill(std::begin(root.segments), std::end(root.segments), 1);
		return root;
	}

	template<typename Item, typename Container>
	partition<Item> last_set_partition(Container&& container) {
		partition<Item> root;
		root.elements.resize(container.size());
		root.segments.resize(container.size());
		root.index.resize(root.elements.size());
		std::iota(root.index.begin(), root.index.end(), 0);
		std::copy(std::begin(container), std::end(container), root.elements.begin());
		std::fill(root.segments.begin(), root.segments.end(), 0);
		if (container.size()) root.segments[0] = container.size();
		return root;
	}

	namespace detail {

		//! Increase lexicographic value of lhs with some item from rhs.
		template<typename Item>
		void increase_from_rhs(partition<Item>& curr, size_t lhs_size, size_t rhs_size) {
			auto e_end = curr.elements.end(), epivot = e_end - rhs_size;
			auto i_end = curr.index.end(), ipivot = i_end - rhs_size;

			// function makes some assumptions:
			assert(lhs_size > 0 && rhs_size > 0);
			assert(std::is_sorted(ipivot, i_end));
			assert(std::is_sorted(ipivot - lhs_size, ipivot));
			assert(*(ipivot - lhs_size) < *(i_end - 1));

			// Search lhs for the greatest item X such as to comply with condition X < MAX(rhs).
			// It is possible to collect a superior set of items in lhs by replacing X with a greater item from rhs.
			// To get a succesive set of items in lhs, we should select the smallest item Y such as Y > X.
			auto iX = std::prev(std::upper_bound(ipivot - lhs_size, ipivot, *(i_end-1)));
			auto iY = std::upper_bound(ipivot, i_end, *iX);

			auto eX = e_end - (i_end - iY);
			auto eY = e_end - (i_end - iX);

			std::iter_swap(iX++, iY++);
			std::iter_swap(eY++, eX++);

			size_t lhs_range = ipivot - iX;
			size_t rhs_range = i_end - iY;

			if (lhs_range < rhs_range) {
				std::swap_ranges(iX, ipivot, iY);
				std::swap_ranges(eY, epivot, eX);
				std::rotate(iY, iY + lhs_range, i_end);
				std::rotate(eX, eX + lhs_range, e_end);

			} else {
				std::swap_ranges(iY, i_end, ipivot - rhs_range);
				std::swap_ranges(eX, e_end, epivot - rhs_range);
				std::rotate(iX, ipivot - rhs_range, ipivot);
				std::rotate(eY, epivot - rhs_range, epivot);
			}
		}


		//! decrease lexicographic valut of lhs with some item from rhs
		template<typename Item>
		void decrease_from_rhs(partition<Item>& curr, size_t lhs_size, size_t rhs_size) {
			auto e_end = curr.elements.end(), epivot = e_end - rhs_size;
			auto i_end = curr.index.end(), ipivot = i_end - rhs_size;

			// function makes some assumptions:
			assert(lhs_size > 0 && rhs_size > 0);
			assert(std::is_sorted(ipivot, i_end));
			assert(std::is_sorted(ipivot - lhs_size, ipivot));
			assert(*(ipivot - 1) > *ipivot);

			// Search rhs for the greatest item X such as to comply with condition X < MAX(lhs).
			// It is possible to collect an inferior set of items in lhs by accepting X instead of some greater item.
			// To get a preceding set of items in lhs, we should expel from lhs the smallest item Y such as Y > X.
			auto iY = std::prev(std::upper_bound(ipivot, i_end, *(ipivot - 1)));
			auto iX = std::upper_bound(ipivot - lhs_size, ipivot, *iY);

			auto eX = e_end - (i_end - iX);
			auto eY = e_end - (i_end - iY);

			std::iter_swap(iX++, iY++);
			std::iter_swap(eX++, eY++);

			size_t lhs_range = ipivot - iX;
			size_t rhs_range = i_end - iY;

			if (lhs_range < rhs_range) {
				std::swap_ranges(iX, ipivot, i_end - lhs_range);
				std::swap_ranges(eX, epivot, e_end - lhs_range);
				std::rotate(iY, i_end - lhs_range, i_end);
				std::rotate(eY, e_end - lhs_range, e_end);
			} else {

				std::swap_ranges(iY, i_end, iX);
				std::swap_ranges(eY, e_end, eX);
				std::rotate(iX, iX + rhs_range, ipivot);
				std::rotate(eX, eX + rhs_range, epivot);
			}
		}

	} // detail


	template<typename Item>
	bool next_unordered_partition(partition<Item>& curr) {
		// It is enough to consider only two tailing segments:
		//  lhs (the penultimate one), and rhs (the last one).

		// The outline of the algorithm is as follows:
		// First, try to increase the value of lhs segment by replacing
		//  some of its items with greater items from the segment.
		//  On fail, cut leading item from rhs and push it into lhs back.
		// Devide rhs segment into single-item segments anyway.

		if (curr.segments.empty()) return false;
		auto s_iter = curr.segments.end();
		while (!*--s_iter) *s_iter = 1;
		size_t rhs_size = std::exchange(*s_iter, 1);
		if (s_iter == curr.segments.begin()) return false;

		while (!*--s_iter);
		size_t lhs_size = *s_iter - 1;

		auto i_end = curr.index.end(), ipivot = i_end - rhs_size;
		if (lhs_size > 0 && *(ipivot - lhs_size) < *(i_end - 1)) {
			detail::increase_from_rhs(curr, lhs_size, rhs_size);
		} else {
			// Each item in rhs is smaller than each item in lhs.
			// Increment lhs size and fill it with the smallest items available.
			// Complete the partition by ascending single-item segements.
			*(s_iter + (*s_iter)++) = 0;
			if (lhs_size > 0) {
				auto e_end = curr.elements.end(), epivot = e_end - rhs_size;
				std::rotate(epivot - lhs_size, epivot, e_end);
				std::rotate(ipivot - lhs_size, ipivot, i_end);
				assert(std::is_sorted(ipivot - lhs_size, i_end));
			}
		}

		return true;
	}


	template<typename Item>
	bool prev_unordered_partition(partition<Item>& curr) {
		// To rollback application of the next method,
		//  we have to take into account all the tailing single-item segments (rhs),
		//  and the segment to the left of these segments (rhs).

		// The outline of the algorithm is as follows:
		// First, try to reduce the valus of lhs segment by replacing
		//  some of its items with smaller items from rhs segment.
		//  On fail, cut the tailing item from lhs and push it into rhs front.
		// Combine the items in rhs into a single segment anyway.

		if (curr.segments.empty()) return false;
		auto s_begin = curr.segments.begin(), s_iter = curr.segments.end();
		while (s_iter != s_begin && *--s_iter) *s_iter = 0;
		size_t rhs_size = curr.segments.end() - s_iter - 1;
		if (rhs_size) *std::next(s_iter) = rhs_size;
		if (s_iter == s_begin) return false;

		while (!*--s_iter);
		size_t lhs_size = *s_iter - 1;

		auto i_end = curr.index.end(), ipivot = i_end - rhs_size;
		if (rhs_size > 0 && *(ipivot - 1) > *ipivot) {
			detail::decrease_from_rhs(curr, lhs_size, rhs_size);
		} else {
			// Each item in lhs is smaller than each item in rhs.
			// Decrement size of lhs and fill it with the greatest items available.
			// Complete partition with a single segment, made up of the items left.
			*(s_iter += --*s_iter) = rhs_size + 1;
			if (rhs_size) *++s_iter = 0;
			if (lhs_size) {
				assert(std::is_sorted(ipivot - lhs_size, i_end));
				auto e_end = curr.elements.end(), epivot = e_end - rhs_size;
				std::rotate(epivot - lhs_size, e_end - (lhs_size - 1), e_end);
				std::rotate(ipivot - lhs_size, i_end - (lhs_size - 1), i_end);
			}
		}

		return true;
	}


	namespace detail {

		/// Arrange items in rhs of the partition in ascending order.
		template<typename Item>
		void arrange_rhs_up(partition<Item>& curr, size_t rhs_size) {
			auto s_end = curr.segments.end(), s_iter = s_end - rhs_size;
			if (*s_iter == rhs_size) return; // prevent double reverse

			auto e_end = curr.elements.end(), e_iter = e_end - rhs_size;
			auto i_end = curr.index.end(), i_iter = i_end - rhs_size;

			while (s_iter != s_end) {
				std::reverse(i_iter, i_iter + *s_iter);
				std::reverse(e_iter, e_iter + *s_iter);

				i_iter += *s_iter;
				e_iter += *s_iter;
				s_iter += *s_iter;
			}

			std::reverse(e_end - rhs_size, e_end);
			std::reverse(i_end - rhs_size, i_end);
		}

		/// Arrange items in rhs of the partition in descending order.
		template<typename Item>
		void arrange_rhs_down(partition<Item>& curr, size_t rhs_size) {
			auto s_end = curr.segments.end(), s_iter = s_end - rhs_size;
			if (*s_iter == rhs_size) return; // prevent double reverse

			auto e_end = curr.elements.end(), e_iter = e_end - rhs_size;
			auto i_end = curr.index.end(), i_iter = i_end - rhs_size;

			std::reverse(e_iter, e_end);
			std::reverse(i_iter, i_end);

			while (s_iter != s_end) {
				std::reverse(i_iter, i_iter + *s_iter);
				std::reverse(e_iter, e_iter + *s_iter);

				i_iter += *s_iter;
				e_iter += *s_iter;
				s_iter += *s_iter;
			}
		}

	} // detail


	template<typename Item>
	bool next_ordered_partition(partition<Item>& curr) {
		// To get the next ordered partition of a set we check
		//  if there is a superior allocation of items for the given
		//  set of segments, and modify this set on fail.
		// Thus, we may have to check allocation in multiple segments.

		// The idea is to search partition for such a pair of its components as to
		//  increase value of the first component using some items from the second one
		//  in the same way, we do in case of unordered patitioning.

		// We refer the right-most segment, which is possible to increase
		// by some items to the right of it -- as lhs, the set of these items -- as rhs,
		//  and the position lhs is ended and rhs is started -- as a pivot point.

		// THe outline of the algorithm is as follows:
		// First, we try to find an appropriate pivot point, lhs and rhs.
		// Next, we rearrange the items in rhs in an ascending order.
		// Rearrangement allows us to apply the algorithm of unordered partitioning,
		//  in case we succeeded to find the appropriate pivot, lhs and rhs, and
		//  enables changing of segment sized without moving any items, otherwise.

		if (curr.segments.empty()) return false;
		auto s_begin = curr.segments.begin(), s_iter = curr.segments.end();
		auto i_end = curr.index.end(), ipivot = i_end;

		while (!*--s_iter);
		while (true) {
			size_t rhs_max = *(ipivot - 1);
			ipivot -= *s_iter;
			if (s_iter == s_begin) break;
			while (!*--s_iter);
			size_t lhs_min = *(ipivot - *s_iter);
			if (lhs_min < rhs_max) break;
		}

		detail::arrange_rhs_up(curr, i_end - ipivot);
		assert(std::is_sorted(ipivot, i_end));

		if (ipivot != curr.index.begin()) {
			detail::increase_from_rhs(curr, *s_iter, i_end - ipivot);
		} else {

			// Use items of the tailing segment to increment size of previos
			//  segment and construct a bunch of single-item segments.
			s_iter = curr.segments.end();
			while (!*--s_iter) *s_iter = 1;
			*s_iter = (s_iter == s_begin);
			if (*s_iter) return false;

			while (!*--s_iter);
			++*s_iter;
		}

		return true;
	}


	template<typename Item>
	bool prev_ordered_partition(partition<Item>& curr) {
		// To revert the effect of the next method,
		//  we use reduction to unordered partitioning as well.
		// The difference is we use items from rhs to reduce value of lhs,
		//  not to increase it, as we do in a next method.

		// The outline of the algorithm is as follows:
		// First we try to find an appropriate pivot point, lhs and rhs.
		// The elements in rhs are already in ascending order, thus
		// If succeded, we apply the algorithm of unordered partitioning.
		// Otherwise, we are safe to change the segment sizes.
		// Finally, we rearrange items in rhs in descending order
		//  appropariately for the given set of segments.

		if (curr.segments.empty()) return false;
		auto s_begin = curr.segments.begin(), s_iter = curr.segments.end();
		auto i_end = curr.index.end(), ipivot = i_end;

		while (!*--s_iter);
		while (true) {
			ipivot -= *s_iter;
			size_t rhs_min = *ipivot;
			if (s_iter == s_begin) break;
			while (!*--s_iter);
			size_t lhs_max = *(ipivot - 1);
			if (lhs_max > rhs_min) break;
		}

		if (ipivot != curr.index.begin()) {
			detail::decrease_from_rhs(curr, *s_iter, i_end - ipivot);
		} else {

			// Use tailing single-item segments and the last item of
			//  previos segment to construct a new tailing segment.
			s_iter = curr.segments.end();
			while (s_iter != s_begin && *--s_iter) *s_iter = 0;
			*s_iter = curr.segments.end() - s_iter;
			if (s_iter == s_begin) return false;

			while (!*--s_iter);
			--*s_iter;
		}

		assert(std::is_sorted(ipivot, i_end));
		detail::arrange_rhs_down(curr, i_end - ipivot);
		return true;
	}


	template<typename Item, typename Container, typename Relation>
	poset<Item> make_poset(Container&& vertices, Relation&& arcs) {
		poset<Item> PS;

		auto& relation = PS.relation;
		auto& elements = PS.ext.elements;
		auto& index = PS.ext.index;

		index.resize(vertices.size());
		std::iota(index.begin(), index.end(), 0);
		std::unordered_set<size_t> V(index.begin(), index.end());

		auto e_begin = std::begin(vertices);
		auto e_end = std::end(vertices);
		for(auto &arc : arcs) {
			size_t source = std::distance(e_begin, std::find(e_begin, e_end, arc.first));
			size_t target = std::distance(e_begin, std::find(e_begin, e_end, arc.second));
			relation.emplace(source, target);
		}

		size_t rank = index.size();
		std::deque<size_t> chain;
		auto A = relation;

		while (A.size()) {
			chain.push_back(*V.cbegin());

			while (chain.size()) {
				size_t last = chain.back();
				auto iter = A.lower_bound({last, 0});

				for(; iter != A.end() && iter->first == last; iter = A.erase(iter)) {
					assert(!std::count(chain.cbegin(), chain.cend(), iter->second));
					if (V.count(iter->second)) {
						chain.push_back(iter->second);
						A.erase(iter);
						break;
					}
				}

				if (last == chain.back()) {
					index[last] = --rank;
					chain.pop_back();
					V.erase(last);
				}
			}
		}

		// take care of standalone vertices
		for(auto v : V) index[v] = --rank;
		// all vertices should be cared of
		assert(rank == 0);

		// copy elements in appropriate order
		elements.resize(index.size());
		while (e_begin != e_end)
			elements[index[rank++]] = *e_begin++;

		// actualize the relation
		std::swap(relation, A);
		for(auto &x : A)
			relation.emplace(index[x.first], index[x.second]);

		// restore index after the transformation
		std::iota(index.begin(), index.end(), 0);
		return PS;
	}


	template<typename Item>
	extension<Item> first_poset_extension(const poset<Item>& ps) {
		return ps.ext;
	}

	template<typename Item>
	extension<Item> last_poset_extension(const poset<Item>& ps) {
		auto root = first_poset_extension(ps);
		prev_poset_extension(root, ps);
		return root;
	}


	// Generate linear extension of a partially ordered set using
	// efficient algorithm by Akimitsu Ono and Shin-ichi Nakano from
	// a paper "Constant Time Generation of Linear Extensions" (2005).
	// The algorithm requires O(1) to generate each sequential extension.

	template<typename Item>
	bool next_poset_extension(extension<Item>& ext, const poset<Item>& ps) {
		auto swap_unrelated = [&] (size_t pos) {
			if (!ps.relation.count({ext.index[pos], ext.index[pos+1]})) {
				std::swap(ext.elements[pos], ext.elements[pos+1]);
				std::swap(ext.index[pos], ext.index[pos+1]);
			} else return false;
			return true;
		};

		size_t max_lvl = ext.index.size() - 1;
		size_t lvl = 0, pos = 0;
		while (true) {

			// Find out the level of current extension.
			while (lvl < max_lvl && lvl == ext.index[lvl]) ++lvl;

			// Search for children at the lower levels.
			// Starting level is next to the previos attempt.
			while (pos != lvl) if (swap_unrelated(pos++)) return true;

			// Stop when the root extension have
			//  no more children to enumerate.
			if (pos == max_lvl) break;

			// Find out current position.
			while (lvl != ext.index[++pos]);

			// Search for the children with superior position.
			if (pos < max_lvl && swap_unrelated(pos)) return true;

			// Rollback to ancestor and search it for relatives.
			std::rotate(&ext.elements[lvl], &ext.elements[pos], &ext.elements[pos+1]);
			std::rotate(&ext.index[lvl], &ext.index[pos], &ext.index[pos+1]);

			// Set the appropriate starting point for the ongoing
			//  search of the next child of the parent node.
			pos = lvl + 1;
		}

		return false;
	}


	template<typename Item>
	bool prev_poset_extension(extension<Item>& ext, const poset<Item>& ps) {
		size_t max_lvl = ext.index.size() - 1;
		size_t lvl = 0, pos = 0;

		// Find out the level of current extension.
		while (lvl < max_lvl && lvl == ext.index[lvl]) ++lvl;
		bool status = (lvl != max_lvl);

		if (lvl < max_lvl) {
			// Find out a position of a current extension.
			pos = lvl; while (lvl != ext.index[++pos]);

			// Swap elements to move to the next sibling.
			std::swap(ext.elements[pos-1], ext.elements[pos]);
			std::swap(ext.index[pos-1], ext.index[pos]);
		}

		// Deepdive to the youngest successor.
		// Have to look through a bunch of levels.
		while (lvl) {

			// Search for a child with the biggest level first.
			while (--lvl && ps.relation.count({ext.index[lvl], ext.index[lvl+1]}));
			if (ps.relation.count({ext.index[lvl], ext.index[lvl+1]})) break;

			// Serch for a child with the highest position.
			for(pos = lvl + 1; pos <= max_lvl; ++pos)
				if (ps.relation.count({ext.index[lvl], ext.index[pos]})) break;

			// Move to the youngest successor at the level.
			std::rotate(&ext.elements[lvl], &ext.elements[lvl+1], &ext.elements[pos]);
			std::rotate(&ext.index[lvl], &ext.index[lvl+1], &ext.index[pos]);
		}

		return status;
	}


	template<typename Item>
	partition<Item> first_poset_partition(poset<Item>& ps) {
		partition<Item> root;
		*(extension<Item>*)(&root) = ps.ext;
		root.segments.resize(root.index.size());
		std::fill(root.segments.begin(), root.segments.end(), 1);
		return root;
	}

	template<typename Item>
	partition<Item> last_poset_partition(poset<Item>& ps) {
		auto root = first_poset_partition(ps);
		prev_poset_partition(root, ps);
		return root;
	}


	template<typename Item>
	bool next_poset_partition(partition<Item>& curr, poset<Item>& ps) {
		if (curr.segments.empty()) return false;
		auto s_iter = curr.segments.end();
		while (!*--s_iter);

		auto s_begin = curr.segments.begin();
		auto i_iter = curr.index.end();
		while (s_iter != s_begin) {
			i_iter -= *s_iter;
			while (!*--s_iter);

			// items in a segment have increasing indexes
			if (*i_iter < *std::prev(i_iter)) continue;

			auto lhs = i_iter - *s_iter;
			// segment never includes items, coupled by relation of the poset
			while (lhs != i_iter && !ps.relation.count({*lhs, *i_iter})) ++lhs;
			if (lhs != i_iter) continue;

			*(s_iter += (*s_iter)++) = 0;
			std::fill(++s_iter, curr.segments.end(), 1);
			return true;
		}

		std::fill(s_begin, curr.segments.end(), 1);
		return next_poset_extension(*(extension<Item>*)(&curr), ps);
	}


	template<typename Item>
	bool prev_poset_partition(partition<Item>& curr, poset<Item>& ps) {
		if (curr.segments.empty()) return false;
		auto s_begin = curr.segments.begin();
		auto s_iter = curr.segments.end();
		while (--s_iter != s_begin && *s_iter);
		bool status = (s_iter != s_begin);

		if (!status) {
			// advance extension if no segement has multiple items
			status = prev_poset_extension(*(extension<Item>*)(&curr), ps);
		} else {
			// reduce the last segment with multiple items
			while (!*--s_iter); s_iter += --(*s_iter);
		}

		// try to join items along the rest of extension
		auto i_iter = curr.index.begin() + (s_iter - s_begin);
		for(; i_iter != curr.index.end(); s_iter += *s_iter) {

			// trying to expand segment as much as possible
			for(*s_iter = 1; ++i_iter != curr.index.end(); ) {

				// items in a segment have increasing indexes
				if (*std::prev(i_iter) > *i_iter) break;

				auto lhs = i_iter - *s_iter;
				// segment never includes items, coupled by relation of the poset
				while (lhs != i_iter && !ps.relation.count({*lhs, *i_iter})) ++lhs;
				if (lhs != i_iter) break;

				// add item to the segment
				*(s_iter + (*s_iter)++) = 0;
			}
		}

		return status;
	}

} // partition_lib
