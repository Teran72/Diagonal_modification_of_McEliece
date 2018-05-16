#ifndef GALOIS
#define GALOIS

#include <iostream>

namespace galois {

	struct Galois {
	public:
		Galois(unsigned int num = 0, unsigned int poly = 0);

		Galois(const Galois& galois);

		Galois& operator=(const Galois& galois);

		~Galois();

		Galois& operator+=(const Galois& galois);

		Galois& operator-=(const Galois& galois);

		Galois& operator*=(const Galois& galois);

		Galois& operator/=(const Galois& galois);

		Galois operator+() const;

		Galois operator-() const;

		Galois inv() const;

		unsigned int get_val() const;

		void copy_poly(const Galois& galois);

		bool isZero() const;

		bool compare(const Galois& galois) const;

		void write(bool show_binary, bool show_poly, std::ostream* outStream = &std::cout) const;

		void read(unsigned int _poly, std::istream* inStream = &std::cin);

		void write(std::ostream* outStream = &std::cout) const;

		void read(std::istream* inStream = &std::cin);

		static Galois rand(unsigned int poly = 0);

		static void set_global_poly(unsigned int poly);

		static void set_global_poly(const Galois& galois);

		static void stash_global_poly(unsigned int poly); //new

		static void unstash_global_poly();                //new

		static void set_binary_mode(bool show_binary);

		static void set_poly_mode(bool show_poly);

	private:
		static const int max_deg = 31;
		static unsigned int global_poly;
		static std::vector<unsigned int> stack_poly;
		static bool mode_show_binary;
		static bool mode_show_poly;

		unsigned int poly;
		unsigned int val;

		void normalize();
	};

	Galois operator+(Galois a, Galois const& b);

	Galois operator-(Galois a, Galois const& b);

	Galois operator*(Galois a, Galois const& b);

	Galois operator/(Galois a, Galois const& b);

	bool operator==(const Galois& a, const Galois& b);

	bool operator!=(const Galois& a, const Galois& b);

	std::ostream& operator<<(std::ostream& outStream, const Galois& galois);

	std::istream& operator>>(std::istream& inStream, Galois& galois);

} // galois

#endif // !GALOIS
