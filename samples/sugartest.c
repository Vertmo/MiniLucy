typedef struct {
	int _var1;
} test_arrow_mem;

typedef struct {
	int z;
} test_arrow_out;

void test_arrow_reset(test_arrow_mem* _self) {
 	_self->_var1 = 1;
}

void test_arrow_step(int x, test_arrow_mem* _self, test_arrow_out* _out) {
 	_out->z = (_self->_var1 ? x : (2 * x));
	_self->_var1 = 0;
}

typedef struct {
	int _var2;
} test_arrow_clock_mem;

typedef struct {
	int z;
} test_arrow_clock_out;

void test_arrow_clock_reset(test_arrow_clock_mem* _self) {
 	_self->_var2 = 1;
}

void test_arrow_clock_step(int x, int b, test_arrow_clock_mem* _self, test_arrow_clock_out* _out) {
 	if (b) {
		_out->z = (_self->_var2 ? x : (2 * x));
		_self->_var2 = 0;
	} else {

	}
}
