#include <iostream>
#include <cstdlib>
#include <stdexcept>
#include <algorithm>
#include "galois.hpp"

using namespace std;
using namespace galois;


unsigned int Galois::global_poly = 3;
vector<unsigned int> Galois::stack_poly(0);
bool Galois::mode_show_binary = true;
bool Galois::mode_show_poly = false;


Galois::Galois(unsigned int num, unsigned int _poly)
	: val(num) {
	poly = _poly;
	if (!poly) {
		poly = global_poly;
	}
	normalize();
}

Galois::Galois(const Galois& galois) {
	poly = galois.poly;
	val = galois.val;
}

Galois& Galois::operator=(const Galois& galois) {
	if (&galois != this) {
		poly = galois.poly;
		val = galois.val;
	}
	return *this;
}

Galois::~Galois() {}

Galois& Galois::operator+=(const Galois& galois) {
	if (poly != galois.poly) {
		throw std::domain_error("Operands are from different fields");
	}

	val ^= galois.val;
	return *this;
}

Galois& Galois::operator-=(const Galois& galois) {
	if (poly != galois.poly) {
		throw std::domain_error("Operands are from different fields");
	}

	val ^= galois.val;
	return *this;
}

Galois& Galois::operator*=(const Galois& galois) {
	if (poly != galois.poly) {
		throw std::domain_error("Operands are from different fields");
	}

	unsigned int res = 0;
	unsigned int b = galois.val;
	int deg_p = max_deg;

	while (!(poly >> deg_p)) {
		deg_p--;
	}

	unsigned int mask = (poly >> deg_p) << deg_p;

	while (val) {
		if (val & 1) {
			res ^= b;
		}
		b <<= 1;
		if (mask & b) {
			b ^= poly;
		}
		val >>= 1;
	}

	val = res;

	return *this;
}

Galois& Galois::operator/=(const Galois& galois) {
	if (poly != galois.poly) {
		throw std::domain_error("Operands are from different fields");
	}

	*this *= galois.inv();

	return *this;
}

Galois Galois::operator+() const {
	return *this;
}

Galois Galois::operator-() const {
	return *this;
}
	
bool Galois::isZero() const {
	return !val;
}

unsigned int Galois::get_val() const {
	return val;
}

void Galois::copy_poly(const Galois& galois) {
	poly = galois.poly;
}

Galois Galois::inv() const {
	if (isZero()) {
		throw overflow_error("Divide by zero exception");
	}
	unsigned int a = poly;
	unsigned int b = val;
	unsigned int v_in_a = 0;
	unsigned int v_in_b = 1;
	int deg_a = max_deg;
	int deg_b = max_deg;

	while (!(b >> deg_b)) {
		deg_b--;
	}
	while (a) {
		while (!(a >> deg_a)) {
			deg_a--;
		}
		if (deg_a >= deg_b) {
			a ^= (b << (deg_a - deg_b));
			v_in_a ^= v_in_b << (deg_a - deg_b);
		} else {
			swap(a, b);
			swap(deg_a, deg_b);
			swap(v_in_a, v_in_b);
		}
	}
	if (b != 1) {
		throw overflow_error("Uninvertible element (that is very strange)");
	}
    return Galois(v_in_b, poly);
}

bool Galois::compare(const Galois& galois) const {
	if (poly != galois.poly) {
		throw std::domain_error("Operands are from different fields");
	}
	return val == galois.val;
}

void Galois::write(bool show_binary, bool show_poly, std::ostream* outStream) const {
	if (show_poly) {
		(*outStream) << poly;
	}
	if (show_binary) {
		int deg_p = max_deg;
		while (!(poly >> deg_p)) {
			deg_p--;
		}
		unsigned int mask = (poly >> deg_p) << (deg_p - 1);
		while (mask) {
			(*outStream) << ((mask & val) ? "1" : "0");
			mask >>= 1;
		}
	} else {
		(*outStream) << val;
	}
}

void Galois::read(unsigned int _poly, std::istream* inStream) {
	if (!_poly) {
		(*inStream) >> poly;
	} else {
		poly = _poly;
	}
	(*inStream) >> val;
    normalize();
}

void Galois::write(std::ostream* outStream) const {
	write(Galois::mode_show_binary, Galois::mode_show_poly, outStream);
}

void Galois::read(std::istream* inStream) {
	read(Galois::global_poly, inStream);
}


Galois Galois::rand(unsigned int poly) {
	if (!poly) {
		poly = global_poly;
	}
	int deg_p = max_deg;
	while (!(poly >> deg_p)) {
		deg_p--;
	}
	unsigned int mask = ((poly >> deg_p) << deg_p) - 1;
	return Galois((std::rand() * RAND_MAX + std::rand()) & mask, poly);
}

void Galois::set_global_poly(unsigned int poly) {
	if (!poly) {
		throw overflow_error("Unacceptable polynom for global_poly");
	}
	Galois::global_poly = poly;
}

void Galois::set_global_poly(const Galois& galois) {
	Galois::global_poly = galois.poly;
}

void Galois::stash_global_poly(unsigned int poly) {
	Galois::stack_poly.push_back(Galois::global_poly);
	Galois::global_poly = poly;
}

void Galois::unstash_global_poly() {
	if (Galois::stack_poly.empty()) {
		Galois::global_poly = 3;
	} else {
		Galois::global_poly = Galois::stack_poly.back();
		Galois::stack_poly.pop_back();
	}
}


void Galois::set_binary_mode(bool show_binary) {
	Galois::mode_show_binary = show_binary;
}

void Galois::set_poly_mode(bool show_poly) {
	Galois::mode_show_poly = show_poly;
}

void Galois::normalize() {
	int deg_p = max_deg;
	int deg_v = max_deg;

	if (!poly) {
		throw overflow_error("Unaccepable polynom in normalization");
	}
	while (!(poly >> deg_p)) {
		deg_p--;
	}
	while (true) {
		while (deg_v >= 0 && !(val >> deg_v)) {
			deg_v--;
		}
		if (deg_v >= deg_p) {
			val ^= poly << (deg_v - deg_p);
		} else {
			break;
		}
	}
}


Galois galois::operator+(Galois a, Galois const& b) {
	return a += b;
}

Galois galois::operator-(Galois a, Galois const& b) {
	return a -= b;
}

Galois galois::operator*(Galois a, Galois const& b) {
	return a *= b;
}

Galois galois::operator/(Galois a, Galois const& b) {
	return a /= b;
}

bool galois::operator==(const Galois& a, const Galois& b) {
	return a.compare(b);
}

bool galois::operator!=(const Galois& a, const Galois& b) {
	return !a.compare(b);
}

std::ostream& galois::operator<<(std::ostream& outStream, const Galois& galois) {
	galois.write(&outStream);
	return outStream;
}

std::istream& galois::operator>>(std::istream& inStream, Galois& galois) {
	galois.read(&inStream);
	return inStream;
}
