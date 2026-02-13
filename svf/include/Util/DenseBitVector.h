//===- DenseBitVector.h - Efficient dense bit vector for SVF --*- C++ -*-===//
//
// A self-contained dense bit vector implementation with word-level operations.
// Modeled after LLVM's BitVector but without LLVM dependencies so it can be
// used in SVF core modules.
//
// Key design choices (matching LLVM BitVector):
//   - Word-level bulk operations (|=, &=, ==, count, any/none)
//   - clearUnusedBits() after resize/shrink for safe == and hash
//   - find_first / find_next via CTZ (count trailing zeros)
//   - Set-bit iterator for efficient range-for over sparse populations
//   - unionWith returns bool (change detection) — the main hot-path API
//   - Move semantics, swap, reserve
//
//===----------------------------------------------------------------------===//

#ifndef SVF_DENSEBITVECTOR_H
#define SVF_DENSEBITVECTOR_H

#include <cassert>
#include <climits>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <functional>
#include <utility>
#include <vector>

namespace SVF
{

class DenseBitVector
{
public:
    using WordType = uint64_t;
    static constexpr unsigned BitsPerWord = sizeof(WordType) * CHAR_BIT;

private:
    std::vector<WordType> words_;
    unsigned numBits_ = 0;

    static unsigned numWordsForBits(unsigned numBits)
    {
        return (numBits + BitsPerWord - 1) / BitsPerWord;
    }

    static unsigned wordIndex(unsigned bitPos) { return bitPos / BitsPerWord; }
    static unsigned bitInWord(unsigned bitPos) { return bitPos % BitsPerWord; }
    static WordType maskBit(unsigned bitPos)
    {
        return WordType(1) << bitInWord(bitPos);
    }

    /// Zero out any bits in the last word that are beyond numBits_.
    /// This is critical for correctness of ==, hash, count, any/none
    /// after resize-down or flip operations.
    void clearUnusedBits()
    {
        unsigned trailing = numBits_ % BitsPerWord;
        if (trailing && !words_.empty())
            words_.back() &= (WordType(1) << trailing) - 1;
    }

public:
    // ----- Construction / sizing -----

    DenseBitVector() = default;

    explicit DenseBitVector(unsigned numBits)
        : words_(numWordsForBits(numBits), 0), numBits_(numBits)
    {
    }

    /// Construct with numBits all set to \p initVal.
    DenseBitVector(unsigned numBits, bool initVal)
        : words_(numWordsForBits(numBits), initVal ? ~WordType(0) : WordType(0)),
          numBits_(numBits)
    {
        if (initVal)
            clearUnusedBits();
    }

    // Move operations
    DenseBitVector(DenseBitVector&& rhs) noexcept
        : words_(std::move(rhs.words_)), numBits_(rhs.numBits_)
    {
        rhs.numBits_ = 0;
    }

    DenseBitVector& operator=(DenseBitVector&& rhs) noexcept
    {
        if (this != &rhs)
        {
            words_ = std::move(rhs.words_);
            numBits_ = rhs.numBits_;
            rhs.numBits_ = 0;
        }
        return *this;
    }

    // Copy operations (defaulted)
    DenseBitVector(const DenseBitVector&) = default;
    DenseBitVector& operator=(const DenseBitVector&) = default;

    void swap(DenseBitVector& rhs) noexcept
    {
        words_.swap(rhs.words_);
        std::swap(numBits_, rhs.numBits_);
    }

    /// Resize to \p newBits bits.  New bits are zero.
    void resize(unsigned newBits)
    {
        words_.resize(numWordsForBits(newBits), 0);
        numBits_ = newBits;
        clearUnusedBits();
    }

    /// Pre-allocate storage for at least \p numBits bits without changing size.
    void reserve(unsigned numBits)
    {
        words_.reserve(numWordsForBits(numBits));
    }

    unsigned size() const { return numBits_; }

    /// Returns true if size is 0 (no bits allocated).
    bool empty() const { return numBits_ == 0; }

    /// Remove all bits (sets size to 0 and frees storage).
    void clear()
    {
        words_.clear();
        numBits_ = 0;
    }

    // ----- Bit manipulation -----

    void set(unsigned idx)
    {
        assert(idx < numBits_ && "DenseBitVector::set out of range");
        words_[wordIndex(idx)] |= maskBit(idx);
    }

    void reset(unsigned idx)
    {
        assert(idx < numBits_ && "DenseBitVector::reset out of range");
        words_[wordIndex(idx)] &= ~maskBit(idx);
    }

    bool test(unsigned idx) const
    {
        assert(idx < numBits_ && "DenseBitVector::test out of range");
        return (words_[wordIndex(idx)] & maskBit(idx)) != 0;
    }

    /// Reset all bits to zero (keeps the current size).
    void resetAll()
    {
        if (!words_.empty())
            std::memset(words_.data(), 0, words_.size() * sizeof(WordType));
    }

    // ----- Bulk word-level operations -----

    /// lhs |= rhs.  Returns true if any bit was newly set.
    /// This is the primary hot-path API for dataflow analysis.
    bool unionWith(const DenseBitVector& rhs)
    {
        if (numBits_ < rhs.numBits_)
            resize(rhs.numBits_);

        bool changed = false;
        const unsigned rhsWords = rhs.words_.size();
        for (unsigned i = 0; i < rhsWords; ++i)
        {
            WordType oldW = words_[i];
            words_[i] |= rhs.words_[i];
            changed |= (words_[i] != oldW);
        }
        return changed;
    }

    /// lhs |= rhs (no change tracking — slightly faster when you don't need it).
    DenseBitVector& operator|=(const DenseBitVector& rhs)
    {
        if (numBits_ < rhs.numBits_)
            resize(rhs.numBits_);

        const unsigned rhsWords = rhs.words_.size();
        for (unsigned i = 0; i < rhsWords; ++i)
            words_[i] |= rhs.words_[i];
        return *this;
    }

    /// lhs &= rhs.  Bits only in lhs become zero.
    DenseBitVector& operator&=(const DenseBitVector& rhs)
    {
        const unsigned thisWords = words_.size();
        const unsigned rhsWords = rhs.words_.size();
        const unsigned common = thisWords < rhsWords ? thisWords : rhsWords;
        unsigned i = 0;
        for (; i < common; ++i)
            words_[i] &= rhs.words_[i];
        // Any bits only in this become zero
        for (; i < thisWords; ++i)
            words_[i] = 0;
        return *this;
    }

    /// lhs ^= rhs.
    DenseBitVector& operator^=(const DenseBitVector& rhs)
    {
        if (numBits_ < rhs.numBits_)
            resize(rhs.numBits_);

        const unsigned rhsWords = rhs.words_.size();
        for (unsigned i = 0; i < rhsWords; ++i)
            words_[i] ^= rhs.words_[i];
        return *this;
    }

    /// Test if any common bits are set (lhs & rhs != 0).
    bool intersects(const DenseBitVector& rhs) const
    {
        const unsigned common = words_.size() < rhs.words_.size()
                                    ? words_.size()
                                    : rhs.words_.size();
        for (unsigned i = 0; i < common; ++i)
            if (words_[i] & rhs.words_[i])
                return true;
        return false;
    }

    bool operator==(const DenseBitVector& rhs) const
    {
        if (numBits_ != rhs.numBits_)
            return false;
        return words_ == rhs.words_;
    }

    bool operator!=(const DenseBitVector& rhs) const { return !(*this == rhs); }

    // ----- Queries -----

    /// Returns true if any bit is set (early exit).
    bool any() const
    {
        for (WordType w : words_)
            if (w)
                return true;
        return false;
    }

    /// Returns true if no bits are set.
    bool none() const { return !any(); }

    /// Returns the number of set bits.
    unsigned count() const
    {
        unsigned c = 0;
        for (WordType w : words_)
            c += static_cast<unsigned>(__builtin_popcountll(w));
        return c;
    }

    /// Find the first set bit, or -1 if none.
    int findFirst() const
    {
        for (unsigned i = 0, n = words_.size(); i < n; ++i)
        {
            if (words_[i])
                return static_cast<int>(i * BitsPerWord + __builtin_ctzll(words_[i]));
        }
        return -1;
    }

    /// Find the next set bit after \p prev, or -1 if none.
    int findNext(int prev) const
    {
        if (prev < 0)
            return -1;
        unsigned next = static_cast<unsigned>(prev) + 1;
        if (next >= numBits_)
            return -1;

        unsigned wi = wordIndex(next);
        unsigned bi = bitInWord(next);

        // Check remaining bits in the current word (mask off lower bits)
        WordType w = words_[wi] >> bi;
        if (w)
            return static_cast<int>(wi * BitsPerWord + bi + __builtin_ctzll(w));

        // Scan subsequent words
        for (unsigned i = wi + 1, n = words_.size(); i < n; ++i)
        {
            if (words_[i])
                return static_cast<int>(i * BitsPerWord + __builtin_ctzll(words_[i]));
        }
        return -1;
    }

    // ----- Hashing -----

    /// Compute a hash over the set bits (for use in unordered_map buckets).
    /// Uses Boost-style hash combining on non-zero words.
    size_t hash() const
    {
        size_t h = 0;
        for (unsigned i = 0, n = words_.size(); i < n; ++i)
        {
            if (words_[i])
            {
                h ^= std::hash<WordType>{}(words_[i])
                     + 0x9e3779b9u + (h << 6) + (h >> 2);
                h ^= std::hash<unsigned>{}(i)
                     + 0x9e3779b9u + (h << 6) + (h >> 2);
            }
        }
        return h;
    }

    // ----- Raw data access (for advanced callers) -----

    const WordType* data() const { return words_.data(); }
    unsigned numWords() const { return words_.size(); }

    // ----- Iterator for set bits -----

    class SetBitsIterator
    {
    public:
        using iterator_category = std::input_iterator_tag;
        using value_type = unsigned;
        using difference_type = std::ptrdiff_t;
        using pointer = const unsigned*;
        using reference = unsigned;

        SetBitsIterator() : bv_(nullptr), idx_(-1) {}
        SetBitsIterator(const DenseBitVector* bv, int idx) : bv_(bv), idx_(idx) {}

        unsigned operator*() const { return static_cast<unsigned>(idx_); }

        SetBitsIterator& operator++()
        {
            idx_ = bv_->findNext(idx_);
            return *this;
        }

        SetBitsIterator operator++(int)
        {
            SetBitsIterator tmp = *this;
            ++(*this);
            return tmp;
        }

        bool operator==(const SetBitsIterator& o) const { return idx_ == o.idx_; }
        bool operator!=(const SetBitsIterator& o) const { return idx_ != o.idx_; }

    private:
        const DenseBitVector* bv_;
        int idx_;
    };

    /// Range-for support: iterates over set bit positions.
    SetBitsIterator begin() const { return SetBitsIterator(this, findFirst()); }
    SetBitsIterator end() const { return SetBitsIterator(this, -1); }
};

} // namespace SVF

#endif // SVF_DENSEBITVECTOR_H
