#include <iostream>
#include <cmath>
#include <chrono>
#include <climits>

using namespace std;

constexpr unsigned long long GB = 1073741824;
void* raw;
unsigned long long reqSize;

int currPower(long long x) // if x is not a power of 2 returns -1
{
	if (x == 1)
		return 0;
	if (x % 2 == 1)
		return -1;
	int i = 0;
	while (x > 1)
	{
		++i;
		x = x >> 1;
	}
	return i;
}

long long nextPower(const long long x) // if x is a power of 2 returns x
{
	long long value = 1;
	while (value < x)
		value = value << 1;
	return value;
}

long long previousPower(const long long x)
{
	long long value = 1;
	while (value < x)
		value = value << 1;
	if (value == x)
		return value;
	return (value >> 1);
}

int leftIndex(const int i)
{
	return 2 * i + 1;
}

int rightIndex(const int i)
{
	return 2 * i + 2;
}

int buddyIndex(const int i)
{
	if (i % 2 == 0)
		return i - 1;
	return i + 1;
}

int parentIndex(const int i)
{
	return (i - 1) / 2;
}

struct Block
{
	Block* next;
	Block* prev;
};

constexpr int maxBlockSize = 512;
constexpr int minBlockSize = 32;
constexpr int maxLevel = 9;
constexpr int minLevel = 5;
constexpr int splitMetaBytesPower = maxLevel - minLevel - 3;
constexpr int freeMetaBytesPower = maxLevel - minLevel + 1 - 3;
#define unusableSize (maxBlockSize - reqSize)
#define numOfMinBlocksForUnusable = (unusableSize / minBlockSize) + 1;
constexpr int splitMetaInBits = (1 << splitMetaBytesPower) * 8;
constexpr int freeMetaInBits = (1 << freeMetaBytesPower) * 8;
constexpr int metaSizeInBytes = (1 << splitMetaBytesPower) + (1 << freeMetaBytesPower);
constexpr int metaSizeInBits = metaSizeInBytes * 8;
#define initSize (unusableSize + metaSizeInBytes + (maxLevel - minLevel + 1) * 8)
constexpr int numOfMinBlocksForMeta = (metaSizeInBytes / minBlockSize) + 1;
#define numOfMinBlocksForInit = ceil((double)initSize / (double)minBlockSize);
constexpr int h = maxLevel - minLevel + 1;
#define metaStart (unsigned char*)raw
#define ptrsStart ((unsigned char*)raw + metaSizeInBytes)
#define freeStart ((unsigned char*)metaStart + (1 << splitMetaBytesPower))

class Allocator
{
public:
	Allocator()
	{
		init();
	}

	void init()
	{
		for (auto i = 0; i < h; ++i)
			setFreeLists(i, nullptr);
		int flag;
		for (auto i = 0; i < h; ++i)
		{
			auto curSize = 0;
			auto blkSize = blockSize(i);
			auto startIndex = (1 << i) - 1;
			auto index = startIndex;
			flag = 1;
			while (curSize < initSize)
			{
				if (i == h - 1)
					toggleFree(index);
				else
				{
					toggleSplit(index);
					toggleFree(index);
				}
				if (i != 0 && i != h - 1)
				{
					if (flag % 2 == 1)
					{
						void* buddyPtr = ptrFromIndex(buddyIndex(index));
						setFreeLists(i, buddyPtr);
					}
					else 
					{
						setFreeLists(i,nullptr);
					}
				}
				++flag;
				curSize += blkSize;
				++index;
			}
		}
	}

	int getLevel(const int i) const
	{
		return floor(log2(i));
	}

	int distance(const int i) const
	{
		return (i - ((1 << static_cast<int>(floor(log2(i)))) - 1));
	}

	static int blockSize(const int currLevel)
	{
		return 1 << (maxLevel - currLevel);
	}

	void* ptrFromIndex(const int i) const
	{
		return static_cast<unsigned char*>(raw) + (blockSize(getLevel(i)) * distance(i)) - (maxBlockSize - reqSize);
	}

	int getLevelFromSize(const size_t size) const
	{
		return maxLevel - log2(size);
	}

	static void setSplit(const int i)
	{
		static_cast<unsigned char*>(metaStart)[i / CHAR_BIT] |= (1 << (i % CHAR_BIT));
	}

	static void*& freeLists(const int i)
	{
		return *reinterpret_cast<void**>((unsigned char*)ptrsStart + i * CHAR_BIT);
	}

	static void setFreeLists(const int i, void* ptr)
	{
		freeLists(i) = ptr;
	}

	static void toggleSplit(const int i)
	{
		static_cast<unsigned char*>(metaStart)[i / CHAR_BIT] ^= (1 << (i % CHAR_BIT));
	}

	static void toggleFree(const int i)
	{
		((unsigned char*)freeStart)[i / CHAR_BIT] ^= (1 << (i % CHAR_BIT));
	}

	static bool isSplit(const int i)
	{
		auto* cptr = static_cast<unsigned char*>(metaStart);
		const auto byte = cptr[i / CHAR_BIT];
		return byte & (1 << (i % CHAR_BIT));
	}

	static bool isFree(const int i)
	{
		auto* cptr = static_cast<unsigned char*>(freeStart);
		const auto byte = cptr[i / CHAR_BIT];
		return !(byte & (1 << (i % CHAR_BIT)));
	}

	Block* getBlock(const size_t size) const
	{
		if (size >= maxBlockSize)
		{
			cout << "out of memory" << endl;
			return nullptr;
		}
		const auto level = getLevelFromSize(size);
		if (freeLists(level) == nullptr)
		{
			Block* leftBuddy = getBlock(size * 2);
			if (leftBuddy == nullptr)
				return nullptr;
			Block* rightBuddy = reinterpret_cast<Block*>(reinterpret_cast<unsigned char*>(leftBuddy) + size);
			setFreeLists(level, rightBuddy);
			static_cast<Block*>(freeLists(level))->next = nullptr;
			static_cast<Block*>(freeLists(level))->prev = nullptr;
			const auto index = indexFromPtrLevel(leftBuddy, level);
			toggleSplit(parentIndex(index));
			toggleFree(index);
			return leftBuddy;
		}
		void* p = freeLists(level);
		setFreeLists(level, static_cast<Block*>(p)->next);
		const auto index = indexFromPtrLevel(p, level);
		toggleFree(index);
		return static_cast<Block*>(p);
	}

	static int indexFromPtrLevel(void* ptr, const int level)
	{
		const long long size = blockSize(level);
		const auto startIndex = (1 << level) - 1;
		for (auto i = 0; i < (1 << level); ++i)
		{
			void* currPtr = static_cast<unsigned char*>(raw) + (i * size) - (maxBlockSize - reqSize);
			if (ptr == currPtr)
				return startIndex + i;
		}
		return 0;
	}

	static int getLevelfromPtr(void* ptr)
	{
		auto n = maxLevel - minLevel;
		while (n > 0)
		{
			if (isSplit(indexFromPtrLevel(ptr, n - 1)))
				return n;
			--n;
		}
		return 0;
	}

	Block* allocate(const size_t size) const
	{
		const auto blockSize = nextPower(size);
		if (blockSize < minBlockSize || blockSize > maxBlockSize)
		{
			cout << "Requested size not acceptable" << endl;
			return nullptr;
		}
		return getBlock(blockSize);
	}

	void deallocate(void* ptr) const
	{
		if (!ptr)
			return;
		const auto level = getLevelfromPtr(ptr);
		long long size = blockSize(level);
		const auto index = indexFromPtrLevel(ptr, level);
		const auto buddyInd = buddyIndex(index);
		Block* buddyPtr = static_cast<Block*>(ptrFromIndex(buddyInd));
		if (isFree(buddyInd))
		{
			Block* curr = static_cast<Block*>(freeLists(level));
			Block* prev = curr;
			while (curr != buddyPtr)
			{
				prev = curr;
				curr = curr->next;
			}
			if (curr == freeLists(level))
			{
				setFreeLists(level, static_cast<Block*>(freeLists(level))->next);
				toggleFree(index);
				const auto parentInd = parentIndex(index);
				toggleSplit(parentInd);
				deallocate(ptrFromIndex(parentInd));
			}
			else
			{
				prev->next = curr->next;
				if (curr->next != nullptr)
					(curr->next)->prev = prev;
				toggleFree(index);
				const auto parentInd = parentIndex(index);
				toggleSplit(parentInd);
				deallocate(ptrFromIndex(parentInd));
			}
		}
		else
		{
			if (freeLists(level) == nullptr)
			{
				setFreeLists(level, ptr);
				static_cast<Block*>(freeLists(level))->next = nullptr;
				static_cast<Block*>(freeLists(level))->prev = nullptr;
				toggleFree(index);
			}
			else
			{
				Block* curr = static_cast<Block*>(freeLists(level));
				curr->prev = static_cast<Block*>(ptr);
				static_cast<Block*>(ptr)->next = curr->next;
				setFreeLists(level, ptr);
				toggleFree(index);
			}
		}
	}
};

int main()
{
	reqSize = 2*GB;
	raw = calloc(1, reqSize);
	auto start = chrono::high_resolution_clock::now();
	auto end = chrono::high_resolution_clock::now();
	start = chrono::high_resolution_clock::now();
	auto* x = malloc(32);
	*reinterpret_cast<int*>(x) = 50;
	end = chrono::high_resolution_clock::now();
	auto duration = chrono::duration_cast<chrono::nanoseconds>(end - start); 
	cout << duration.count() << endl;

	Allocator a;
	for (auto i = 0; i < 16; ++i)
	{
		cout << boolalpha << i << ' ' << a.isSplit(i) << endl;
	}
	//puts("-------------------------");
	for (auto i = 0; i < 32; ++i)
	{
		cout << boolalpha << i << ' ' << a.isFree(i) << endl;
	}
	//a.allocate(32);
	start = chrono::high_resolution_clock::now();
	auto* p1 = a.allocate(32);
	*reinterpret_cast<int*>(p1) = 50;
	end = chrono::high_resolution_clock::now();
	duration = chrono::duration_cast<chrono::nanoseconds>(end - start); 
	cout << duration.count() << endl;
	//a.deallocate(p);
	free(raw);
	return 0;
}