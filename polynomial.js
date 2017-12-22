/**
 * @license Polynomial.js v1.4.0 13/12/2017
 *
 * Copyright (c) 2015, Robert Eisele (robert@xarg.org)
 * Dual licensed under the MIT or GPL Version 2 licenses.
 **/

(function(root) {

  "use strict";

  /**
   * The actual field selected
   * 
   * @type Object
   */
  var FIELD = {// Run in R
    "add": function(a, b) {
      return a + b;
    },
    "sub": function(a, b) {
      return a - b;
    },
    "mul": function(a, b) {
      return a * b;
    },
    "div": function(a, b) {
      if (b === 0) {
        throw "DIV/0";
      }
      return a / b;
    },
    "parse": function(x) {
      return parseFloat(x);
    },
    "empty": function(x) {
      return !x; //undefined === x || 0 === x;
    },
    "pow": function(a, b) {
      return Math.pow(a, b);
    },
    "equals": function(a, b) {
      return a == b;
    }
  };

  /**
   * Save the original field for changes
   * 
   * @type Object
   */
  var ORIG_FIELD = FIELD;

  /**
   * The Fraction callback
   * 
   * @type Function
   */
  var Fraction;

  /**
   * The Complex callback
   * 
   * @type Function
   */
  var Complex;

  /**
   * The Quaternion callback
   * 
   * @type Function
   */
  var Quaternion;

  var STR_REGEXP = /([+-]?)(?:([^+x-]+)?(?:x(?:\^([\d\/]+))?)|([^+x-]+))/g;

  /**
   * The constructor function
   * 
   * @constructor
   * @param {String|Object|number} x The init polynomial
   */
  function Polynomial(x) {

    if (!(this instanceof Polynomial)) {
      return new Polynomial(x);
    }
    this['coeff'] = parse(x);
  }

  // Trace poly div steps
  Polynomial['trace'] = null;

  /**
   * Calculates the modular inverse
   * 
   * @param {number} z
   * @param {number} n
   * @returns {number}
   */
  var modinv = function(z, n) {

    /**
     *    z * s + n * t = 1 
     * => z * s mod n = 1
     * => z^-1 = s mod n
     */
    var tmp = egcd(z, n);
    if (tmp[0] !== 1) {
      throw "DIV/-";
    }
    return tmp[1];
  };

  /**
   * Calculates the gcd
   * 
   * @param {number} a
   * @param {number} b
   * @returns {number}
   */
  function gcd(a, b) {
    var t;
    while (b) {
      t = a;
      a = b;
      b = t % b;
    }
    return Math.abs(a);
  }

  function clone(x) {

    var res = {};
    for (var i in x) {
      res[i] = x[i];
    }
    return res;
  }

  /**
   * Calculates the extended gcd
   * 
   * @param {number} a
   * @param {number} b
   * @returns {Array}
   */
  var egcd = function(a, b) {

    // gcd = a * s  +  b * t

    var s = 0, t = 1, u = 1, v = 0;
    while (a !== 0) {

      var q = b / a | 0, r = b % a;
      var m = s - u * q, n = t - v * q;

      b = a;
      a = r;
      s = u;
      t = v;
      u = m;
      v = n;
    }
    return [b /* gcd*/, s, t];
  };

  /**
   * Calculates the mathematical modulo
   * 
   * @param {number} n
   * @param {number} m 
   * @returns {number}
   */
  var mod = function(n, m) {

    return (n % m + m) % m;
  };

  /**
   * Calculates the factorial n! / (n - k)!
   * 
   * @param {number} n
   * @param {number} k
   * @returns {number}
   */
  var factorial = function(n, k) {

    var p = 1;
    for (k = n - k; k < n; n--) {
      p *= n;
    }
    return p;
  };

  /**
   * The public coefficient object
   * 
   * @type {Object}
   */
  Polynomial.prototype['coeff'] = {};

  /**
   * Return a dense array of coefficients
   *
   * @type {Array<Object>} Length n+1 array of coefficients
   */
  Polynomial.prototype['coeffArray'] = function() {
    var coeffs = this['coeff'];
    var deg = degree(coeffs);
    var coeffArr = new Array(deg+1);

    for (var i=0; i<=deg; i++) {
      if ( coeffs.hasOwnProperty(i) ) {
        coeffArr[i] = coeffs[i];
      } else {
        coeffArr[i] = 0.0;
      }
    }

    return coeffArr;
  };

  /**
   * Combines the keys of two objects
   * 
   * @param {Object} a
   * @param {Object} b
   * @returns {Object}
   */
  function keyUnion(a, b) {

    var k = {};
    for (var i in a) {
      k[i] = 1;
    }
    for (var i in b) {
      k[i] = 1;
    }
    return k;
  }

  /**
   * Gets the degree of the actual polynomial
   * 
   * @param {Object} x
   * @returns {String|number}
   */
  function degree(x) {

    var i = Number.NEGATIVE_INFINITY;

    for (var k in x) {
      if (!FIELD['empty'](x[k]))
        i = Math.max(k, i);
    }
    return i;
  }

  /**
   * Helper function for division
   * 
   * @param {Object} x The numerator coefficients
   * @param {Object} y The denominator coefficients
   * @returns {Object}
   */
  var div = function(x, y) {

    var r = {};

    var i = degree(x);
    var j = degree(y);
    var trace = [];

    while (i >= j) {

      var tmp = r[i - j] = FIELD['div'](x[i] || 0, y[j] || 0);

      for (var k in y) {
        x[+k + i - j] = FIELD['sub'](x[+k + i - j] || 0, FIELD['mul'](y[k] || 0, tmp));
      }

      if (Polynomial['trace'] !== null) {

        var tr = {};
        for (var k in y) {
          tr[+k + i - j] = FIELD['mul'](y[k] || 0, tmp);
        }
        trace.push(new Polynomial(tr));
      }

      i = degree(x);
    }

    // Add rest
    if (Polynomial['trace'] !== null) {
      trace.push(new Polynomial(x));
      Polynomial['trace'] = trace;
    }
    return r;
  };

  function parseExp(sgn, exp) {

    exp = String(exp).match(/[^*/]+|[*/]/g);

    var num = FIELD['parse'](sgn + exp[0]);

    for (var i = 1; i < exp.length; i += 2) {

      if (exp[i] === '*') {
        num = FIELD['mul'](num, FIELD['parse'](exp[i + 1] || 1));
      } else if (exp[i] === '/') {
        num = FIELD['div'](num, FIELD['parse'](exp[i + 1] || 1));
      }
    }
    return num;
  }

  /**
   * Parses the actual number
   * 
   * @param {String|Object|null|number} x The polynomial to be parsed
   * @returns {Object}
   */
  var parse = function(x) {

    var ret = {};

    if (x === null || x === undefined) {
      x = 0;
    }

    switch (typeof x) {

      case "object":

        if (x['coeff']) {
          x = x['coeff'];
        }

        if (Fraction && x instanceof Fraction || Complex && x instanceof Complex || Quaternion && x instanceof Quaternion) {
          ret[0] = x;
        } else
          // Handles Arrays the same way
          for (var i in x) {

            if (!FIELD['empty'](x[i])) {
              ret[i] = FIELD['parse'](x[i]);
            }
          }
        return ret;

      case  "number":
        return {'0': FIELD['parse'](x)};

      case "string":

        var tmp, num, exp;

        while (null !== (tmp = STR_REGEXP['exec'](x))) {

          num = 1;
          exp = 1;

          if (tmp[4] !== undefined) {
            num = tmp[4];
            exp = 0;
          } else if (tmp[2] !== undefined) {
            num = tmp[2];
          }

          num = parseExp(tmp[1], num);

          // Parse exponent
          if (tmp[3] !== undefined) {
            exp = parseInt(tmp[3], 10);
          }

          if (ret[exp] === undefined) {
            ret[exp] = num;
          } else {
            ret[exp] = FIELD['add'](ret[exp], num);
          }
        }
        return ret;
    }
    throw "Invalid Param";
  };

  /**
   * Calculates the gcd of two polynomials
   * 
   * @param {String|Object} x The denominator polynomial
   * @returns {Polynomial}
   */
  Polynomial.prototype['gcd'] = function(x) {

    var a = clone(this['coeff']);
    var b = parse(x);

    var max;

    while (!isNull(b)) {

      var r = clone(a);

      div(r, b);

      a = b;
      b = r;
    }

    max = lc(a);

    return new Polynomial(monic(a, max));
  };

  /**
   * Negate all coefficients of the polynomial
   * 
   * @returns {Polynomial}
   */
  Polynomial.prototype['neg'] = function() {

    var ret = {};
    var poly = this['coeff'];

    for (var i in poly) {
      ret[i] = FIELD['mul'](poly[i], -1);
    }
    return new Polynomial(ret);
  };

  /**
   * Return the 'reciprocal polynomial', where the coefficients
   * appear in opposite order; i.e. a[i] -> a[n-i].
   * See e.g. https://en.wikipedia.org/wiki/Reciprocal_polynomial
   *
   * @returns {Polynomial}
   */
  Polynomial.prototype['reciprocal'] = function() {

    var ret = {};
    var poly = this['coeff'];
    var n = degree(poly);

    for (var i in poly) {
      ret[n - i] = poly[i];
    }
    return new Polynomial(ret);
  };

  /**
   * Numerically evaluate the polynomial at a specific point x by
   * using Horner's method.
   * See e.g. https://en.wikipedia.org/wiki/Horner%27s_method
   *
   * @param {number} x The point where to evaluate this polynomial
   * @returns {number} The value P(x)
   */
  Polynomial.prototype['eval'] = function(x) {

    var poly = this['coeff'];
    var n = degree(poly);
    var ret = poly[n];

    for (var i = n - 1; i >= 0; i--) {
      ret = FIELD['mul'](ret, x);
      if (!FIELD['empty'](poly[i])) {
        ret = FIELD['add'](ret, poly[i]);
      }
    }
    return ret;
  };

  function lc(poly) {

    var max = null;

    for (var i in poly) {

      if (!FIELD['empty'](poly[i])) {

        if (max === null || +max < +i) {
          max = i;
        }
      }
    }
    return max;
  }

  function monic(a, max) {

    if (max !== null) {

      for (var i in a) {
        a[i] = FIELD['div'](a[i], a[max]);
      }
    }
    return a;
  }

  /**
   * Gets the leading coefficient
   * 
   * @returns {Polynomial}
   */
  Polynomial.prototype['lc'] = function() {

    var max = lc(this['coeff']);

    return this['coeff'][max];
  };

  /**
   * Gets the leading monomial
   * 
   * @returns {Polynomial}
   */
  Polynomial.prototype['lm'] = function() {

    var max = lc(this['coeff']);

    var res = {};

    res[max] = this['coeff'][max];
    return new Polynomial(res);
  };

  /**
   * Divide all coefficients of f by lc(f)
   * 
   * @returns {Polynomial}
   */
  Polynomial.prototype['monic'] = function() {

    return new Polynomial(monic(clone(this['coeff']), lc(this['coeff'])));
  };

  /**
   * Calculates the sum of two polynomials
   * 
   * @param {String|Object} x The summand polynomial
   * @returns {Polynomial}
   */
  Polynomial.prototype['add'] = function(x) {

    var para = parse(x);

    var ret = {};
    var poly = this['coeff'];

    var keys = keyUnion(para, poly);

    for (var i in keys) {
      ret[i] = FIELD['add'](poly[i] || 0, para[i] || 0);
    }
    return new Polynomial(ret);
  };

  /**
   * Calculates the difference of two polynomials
   * 
   * @param {String|Object} x The subtrahend polynomial
   * @returns {Polynomial}
   */
  Polynomial.prototype['sub'] = function(x) {

    var para = parse(x);

    var ret = {};
    var poly = this['coeff'];

    var keys = keyUnion(para, poly);

    for (var i in keys) {
      ret[i] = FIELD['sub'](poly[i] || 0, para[i] || 0);
    }
    return new Polynomial(ret);
  };

  /**
   * Calculates the product of two polynomials
   * 
   * @param {String|Object} x The minuend polynomial
   * @returns {Polynomial}
   */
  Polynomial.prototype['mul'] = function(x) {

    var para = parse(x);

    var ret = {};
    var poly = this['coeff'];

    for (var i in para) {

      i = +i;

      for (var j in poly) {

        j = +j;

        ret[i + j] = FIELD['add'](ret[i + j] || 0, FIELD['mul'](para[i] || 0, poly[j] || 0));
      }
    }
    return new Polynomial(ret);
  };

  /**
   * Calculates the product of the two parameters and adds it to the current number (linear combination)
   * 
   * @param {String|Object} x The first factor polynomial
   * @param {String|Object} y The second factor polynomial
   * @returns {Polynomial}
   */
  Polynomial.prototype['addmul'] = function(x, y) {

    var _x = parse(x);
    var _y = parse(y);

    var res = {};
    for (var i in _x) {

      i = +i;

      for (var j in _y) {
        j = +j;

        res[i + j] = FIELD['add'](res[i + j] || 0, FIELD['mul'](_x[i] || 0, _y[j] || 0));
      }
    }
    return this['add'](res);
  };

  /**
   * Calculates the quotient of two polynomials
   * 
   * @param {String|Object} x The denominator polynomial
   * @returns {Polynomial}
   */
  Polynomial.prototype['div'] = function(x) {

    return new Polynomial(div(clone(this['coeff']), parse(x)));
  };

  /**
   * Calculates the pow of a polynomial to the exponent e
   * 
   * @returns {Polynomial}
   */
  Polynomial.prototype['pow'] = function(e) {

    if (isNaN(e) || e < 0 || e % 1) { // Only integer exponents
      throw "Invalid";
    }

    var res = new Polynomial(1);
    var tmp = this;

    while (e > 0) {

      if (e & 1) {
        res = res['mul'](tmp);
      }
      tmp = tmp['mul'](tmp);
      e >>= 1;
    }
    return res;
  };

  /**
   * Calculates the modulo of a polynomial to another
   * 
   * @param {String|Object} x The second poly
   * @returns {Polynomial}
   */
  Polynomial.prototype['mod'] = function(x) {

    var mod = clone(this['coeff']);

    div(mod, parse(x));

    return new Polynomial(mod);
  };

  /**
   * Calculates the nth derivative of the polynomial
   * 
   * @param {number} n The nth derivative
   * @returns {Polynomial}
   */
  Polynomial.prototype['derive'] = function(n) {

    if (n === undefined) {
      n = 1;
    } else if (n < 0) {
      return null;
    }

    var poly = this['coeff'];
    var ret = {};

    for (var i in poly) {

      if (+i >= n)
        ret[i - n] = FIELD['mul'](poly[i] || 0, factorial(+i, n));
    }
    return new Polynomial(ret);
  };

  /**
   * Calculates the nth integral of the polynomial
   * 
   * @param {number} n The nth integral
   * @returns {Polynomial}
   */
  Polynomial.prototype['integrate'] = function(n) {

    if (n === undefined) {
      n = 1;
    } else if (n < 0) {
      return null;
    }

    var poly = this['coeff'];
    var ret = {};

    for (var i in poly) {
      ret[+i + n] = FIELD['div'](poly[i] || 0, factorial(+i + n, n));
    }
    return new Polynomial(ret);
  };

  /**
   * (Deprecated) alias for 'eval'
   */
  Polynomial.prototype['result'] = Polynomial.prototype['eval'];

  /**
   * Helper for recursively forming polynomials from roots
   *
   * @returns {Polynomial}
   */
  function productHelper(roots) {
    switch (roots.length) {
      case 0:
        return new Polynomial(FIELD['parse'](1.));
      case 1:
        return new Polynomial([ FIELD['mul'](roots[0], -1.), 1.]);
      default: // recurse
        var nLeft = Math.floor(roots.length/2);
        var left  = roots.slice(0, nLeft),
            right = roots.slice(nLeft, roots.length);
      return productHelper(left)['mul'](productHelper(right));
    }
  }

  /**
   * Form a (monic) polynomial out of an array of roots
   *
   * @param {Array<number>} roots - Array of roots
   * @returns {Polynomial} The monic polynomial with those roots
   */
  Polynomial['fromRoots'] = function (roots) {

    var n = roots.length;

    var zero = FIELD['parse'](0.);

    var nonZeroRoots = roots.filter( root => (!(FIELD['equals'](root, zero))) );
    var numZeros = n - nonZeroRoots.length;

    // First we construct the depressed polynomial with a recursive
    // strategy (this minimizes the number of multiplications)
    var dep = productHelper(nonZeroRoots);

    // Now raise the order by including numZeros zeros
    var dcoeff = dep['coeff'];
    var coeff = {};

    for (var i in dcoeff) {
      coeff[numZeros + parseInt(i, 10)] = dcoeff[i];
    }

    return new Polynomial(coeff);
  }

  /******************************************************************/
  /* Complex root-finding using Aberth's method
   * Much of this follows the netlib FORTRAN implementation,
   * see http://www.netlib.org/numeralgo/na10
   * The starting roots and stopping conditions come from the paper
   * "Numerical computation of polynomial zeros by means of Aberth's method"
   * Bini, D.A. Numer Algor (1996) 13: 179.
   * https://doi.org/10.1007/BF02207694
   */

  /**
   * Helper function for Aberth's method of root finding,
   * Aberth correction (improves Newton iteration)
   *
   * @param {Array<Object>} roots Current root estimates
   * @param {number} j Index into roots for correction update
   * @returns {Object} Aberth's correction, sum of 1/(z_j-z_i)
   */
  function Aberth(roots, j) {
    var degree = roots.length;
    var zj = roots[j];
    var Abcorr = Complex.ZERO;

    for (var i=0; i<degree; i++) {

      if (i==j)
        continue;

      Abcorr = Abcorr.add( zj.sub(roots[i]).inverse() );
    };

    return Abcorr;
  }

  /**
   * Helper function for Aberth's method of root finding,
   * Newton correction.
   *
   * @param {Array<Object>} poly Coefficients of P(x)
   * @param {Array<number>} apoly upper bounds on the backward
   *                              perturbation on the coefficients of
   *                              P(x) when applying Ruffini-Horner's
   *                              rule
   * @param {Array<number>} apolyr upper bounds on the backward
   *                               perturbations on the coefficients
   *                               of P(x)
   * @param {Object} z value at which the Newton correction is computed
   * @param {number} radius TODO
   * @param {boolean} again TODO
   * @returns {Object} TODO {'corr', 'again', 'radius'}
   */
  function Newton(poly, apoly, apolyr, z, radius, again) {
    var degree = poly.length - 1;

    var az = z.abs();
    var corr;

    if (az <= 1.) {
      var p = poly[degree];
      var p1 = p;
      var ap = apoly[degree];

      /* This is a slightly more efficient way to compute
       * P(z) and P'(z) at the same time.
       */
      for (var i = degree-1; i >= 1; i--) {
        p = p['mul'](z)['add'](poly[i]);
        p1 = p1['mul'](z)['add'](p);
        ap = ap*az + apoly[i];
      };
      p = p['mul'](z)['add'](poly[0]);
      ap = ap*az + apoly[0];

      corr = p['div'](p1);
      var absp = p.abs();

      again = (absp > (Number.MIN_VALUE + ap));
      if (!again) {
        radius = degree * (absp + ap)/p1.abs();
      };

    } else { /* |z|>1 */
      var zi = z.inverse();
      var azi = 1/az;
      var p = poly[0];
      var p1 = p;
      var ap = apolyr[degree];

      /* This is a slightly more efficient way to compute
       * P(z) and P'(z) at the same time.
       */
      for (var i = degree-1; i>=1; i--) {
        p = p['mul'](zi)['add'](poly[degree-i]);
        p1 = p1['mul'](zi)['add'](p);
        ap = ap*azi+apolyr[i];
      };
      p = p['mul'](zi)['add'](poly[degree]);
      ap = ap*azi + apolyr[0];

      var absp = p.abs();
      again = (absp > (Number.MIN_VALUE + ap));

      var ppsp = p['mul'](z)['div'](p1);
      var den = ppsp['mul'](degree)['sub'](Complex.ONE);
      corr = z['mul'](ppsp['div'](den));

      if (!again) {
        radius = ppsp.abs() + (ap*az)/p1.abs();
        radius = degree*radius/den.abs();
        radius = radius*az;
      };

    };

    return {'corr': corr, 'again': again, 'radius': radius};

  }

  /**
   * Perform the actual Aberth iteration
   *
   * @param {Array<Object>} poly Array of Complex polynomial coefficients
   * @param {number} nitmax The max number of allowed iterations
   * @param {Array<Object>} root Starting guesses for roots
   * @return {Object} TODO {root, radius, err, iter}
   */
  function AberthIterate(poly, nitmax, root) {
    var eps = Number.EPSILON;
    var big = Number.MAX_VALUE;
    var small = Number.MIN_VALUE;

    var deg = poly.length - 1;

    if (Complex.ZERO['equals'](poly[deg])) {
      throw('Inconsistent data: the leading coefficient is zero');
    }
    if (Complex.ZERO['equals'](poly[0])) {
      // TODO: This is from Bini's implementation; but we could simply
      // identify that we have a certain number of roots at the
      // origin and continue.
      throw('The constant term is zero: deflate the polynomial');
    }

    var amax = 0.;
    var apoly = new Array(deg+1), apolyr = new Array(deg+1);
    for (var i=0; i<=deg; i++) {
      apoly[i] = poly[i].abs();
      amax = Math.max(amax, apoly[i]);
      apolyr[i] = apoly[i];
    }
    if (amax >= (big/(deg+1)))
      console.warn('WARNING: COEFFICIENTS TOO BIG, OVERFLOW IS LIKELY');

    for (var i=0; i<=deg; i++) {
      // the magic numbers on the RHS come from Bini
      apolyr[deg-i] = eps*apoly[i]*(3.8*(deg-i)+1.);
      apoly[i] = eps*apoly[i]*(3.8*i+1.);
    };

    if ((apoly[0] == 0) || (apoly[deg] == 0)) {
      console.warn('WARNING: THE COMPUTATION OF SOME INCLUSION RADIUS MAY FAIL. THIS IS REPORTED BY RADIUS=0');
    }

    var err = new Array(deg), radius = new Array(deg);

    for (var i=0; i<deg; i++) {
      err[i] = true;
      radius[i] = 0.;
    }

    if (nitmax === undefined)
      nitmax = 30;

    // Start Aberth's iterations

    var iter, nzeros = 0;

    // Label for breaking if we converge before nitmax
    iterloop:
    for (iter = 1; iter <= nitmax; iter++) {
      for (var i=0; i < deg; i++) {
        if (err[i]) {
          var newt = Newton(poly, apoly, apolyr, root[i], radius[i], err[i]);
          // unpack results (I don't want to be FORTRAN-y)
          var corr = newt['corr'];
          err[i] = newt['again'];
          if (!err[i]) radius[i] = newt['radius'];
          if (err[i]) {
            var Abcorr = Aberth(root, i);
            root[i] = root[i]['sub'](corr['div'](Complex.ONE['sub'](corr['mul'](Abcorr))));
          } else {
            nzeros++;
            if (nzeros == deg) break iterloop;
          }
        }
      }
    }
    return {'root': root, 'radius': radius, 'err': err, 'iter': iter};
  }

  /**
   * complexRoots interface. For testing right now. TODO
   */
  Polynomial.prototype['complexRoots'] = function(root) {
    var coeffs = this['coeff'];
    var deg = degree(coeffs);
    var poly = new Array(deg+1), croot = new Array(deg);

    for (var i=0; i<=deg; i++) {
      if ( coeffs.hasOwnProperty(i) ) {
        poly[i] = Complex(coeffs[i]);
      } else {
        poly[i] = Complex.ZERO;
      }
    }

    for (var i=0; i<deg; i++)
      croot[i] = new Complex(root[i]);

    return AberthIterate(poly, 30, root);
  }

  /******************************************************************/

  /**
   * Helper method to stringify
   * 
   * @param {string} fn the callback name
   * @returns {Function}
   */
  var toString = function(fn) {

    /**
     * The actual to string function 
     * 
     * @returns {string|null}
     */
    var Str = function() {

      var poly = this['coeff'];

      var keys = [];
      for (var i in poly) {
        keys.push(+i);
      }

      if (keys.length === 0)
        return "0";

      keys.sort(function(a, b) {
        return a - b;
      });

      var val, str = "";
      for (var k = keys.length; k--; ) {

        var i = keys[k];

        var cur = poly[i];

        val = cur;

        if (val === null || val === undefined)
          continue;

        if (Complex && val instanceof Complex) {

          // Add real part
          if (val['re'] !== 0) {

            if (str !== "" && val['re'] > 0) {
              str += "+";
            }

            if (val['re'] === -1 && i !== 0) {
              str += "-";
            } else if (val['re'] !== 1 || i === 0) {
              str += val['re'];
            }

            // Add exponent if necessary, no DRY, let's feed gzip
            if (i === 1)
              str += "x";
            else if (i !== 0)
              str += "x^" + i;
          }

          // Add imaginary part
          if (val['im'] !== 0) {

            if (str !== "" && val['im'] > 0) {
              str += "+";
            }

            if (val['im'] === -1) {
              str += "-";
            } else if (val['im'] !== 1) {
              str += val['im'];
            }

            str += "i";

            // Add exponent if necessary, no DRY, let's feed gzip
            if (i === 1)
              str += "x";
            else if (i !== 0)
              str += "x^" + i;
          }

        } else {

          val = val.valueOf();

          // Skip if it's zero
          if (val === 0)
            continue;

          // Separate by +
          if (str !== "" && val > 0) {
            str += "+";
          }

          if (val === -1 && i !== 0)
            str += "-";
          else

          // Add number if it's not a "1" or the first position
          if (val !== 1 || i === 0)
            str += cur[fn] ? cur[fn]() : cur['toString']();

          // Add exponent if necessary, no DRY, let's feed gzip
          if (i === 1)
            str += "x";
          else if (i !== 0)
            str += "x^" + i;
        }
      }

      if (str === "")
        return cur[fn] ? cur[fn]() : cur['toString']();

      return str;
    };
    return Str;
  };

  /**
   * Formats the polynomial as a string
   * 
   * @returns {string} The polynomial string
   */
  Polynomial.prototype['toString'] = toString("toString");

  /**
   * Formats the polynomial as a latex representation
   * 
   * @returns {string} The polynomial latex string
   */
  Polynomial.prototype['toLatex'] = toString("toLatex");

  /**
   * Returns the actual polynomial in horner scheme
   * 
   * @returns {string}
   */
  Polynomial.prototype['toHorner'] = function() {

    var poly = this['coeff'];
    var keys = [];
    for (var i in poly) {
      if (!FIELD.empty(poly[i]))
        keys.push(+i);
    }

    if (keys.length === 0)
      return "0";

    keys.sort(function(a, b) {
      return a - b;
    });

    // TODO: DRY, Combine with toString function
    function valToString(val, hasSign) {

      var str = "";

      if (Complex && val instanceof Complex) {

        if (val['im'] === 0) {

          if (val['re'] > 0 && hasSign) {
            str += "+";
          }
          str += val['re'];

        } else if (val['re'] === 0) {

          if (val['im'] === -1) {
            str += "-";
          } else if (val['im'] !== 1) {

            if (val['im'] > 0 && hasSign) {
              str += "+";
            }
            str += val['im'];
          } else {
            if (val['im'] > 0 && hasSign) {
              str += "+";
            }
          }
          str += "i";

        } else {

          if (hasSign) {
            str += "+";
          }

          str += "(";
          str += val.toString();
          str += ")";
        }

        return str;

      } else {

        if (val > 0 && hasSign) {
          str += "+";
        }
        str += val.toString();
      }
      return str;
    }

    function rec(keys, pos) {

      var ndx = keys.length - pos - 1;
      var exp = keys[ndx] - (keys[ndx - 1] || 0);
      var str1 = "";
      var str2 = "";

      if (exp > 0) {
        str1 = "x";

        if (exp > 1) {
          str1 += "^" + exp;
        }
      }

      if (ndx > 0)
        str1 += valToString(poly[keys[ndx - 1]], true);

      if (pos === 0) {
        return valToString(poly[keys[ndx]], false) + str1;
      }

      if (ndx >= 0 && keys[ndx])
        str2 += "(";

      str2 += rec(keys, pos - 1);

      if (ndx >= 0 && keys[ndx])
        str2 += ")";

      str2 += str1;

      return str2;
    }
    return rec(keys, keys.length - 1);
  };

  /**
   * Clones the actual object
   * 
   * @returns {Polynomial}
   */
  Polynomial.prototype['clone'] = function() {
    return new Polynomial(this);
  };

  /**
   * Returns the degree of the polynomial
   * 
   * @returns {number}
   */
  Polynomial.prototype['degree'] = function() {

    return degree(this['coeff']);
  };

  function isNull(r) {

    return degree(r) === Number.NEGATIVE_INFINITY;
  }

  /**
   * Set the field globally
   * 
   * @param {string|Object} field One of: C (complex), H (quaternion), Q (rational), R (real) or an object with methods for field
   */
  Polynomial['setField'] = function(field) {

    // Fields with the same common API
    var F = {
      "Q": Fraction,
      "C": Complex,
      "H": Quaternion
    }[field];

    if (F !== undefined) {

      FIELD = {
        "add": function(a, b) {
          return new F(a)['add'](b);
        },
        "sub": function(a, b) {
          return new F(a)['sub'](b);
        },
        "mul": function(a, b) {
          return new F(a)['mul'](b);
        },
        "div": function(a, b) {
          return new F(a)['div'](b);
        },
        "parse": function(x) {
          return new F(x);
        },
        "empty": function(x) {
          return new F(x)['equals'](0);
        },
        "pow": function(a, b) {
          return new F(a)['pow'](b);
        },
        "equals": function(a, b) {
          return new F(a)['equals'](b);
        }
      };

    } else if (!field || field === 'R') {

      FIELD = ORIG_FIELD;

    } else if (typeof field === 'object') {

      FIELD = field;

    } else if (field.charAt(0) === 'Z') {

      var N = +field.slice(1);

      FIELD = {// Test in Z_n
        "add": function(a, b) {
          return mod(a + b, N);
        },
        "sub": function(a, b) {
          return mod(a - b, N);
        },
        "mul": function(a, b) {
          return mod(a * b, N);
        },
        "div": function(a, b) {
          return mod(a * modinv(b, N), N);
        },
        "parse": function(x) {
          return parseInt(x, 10);
        },
        "empty": function(x) {
          return undefined === x || 0 === x;
        },
        "pow": function(a, b) {

          for (var r = 1; b > 0; a = mod(a * a, N), b >>= 1) {

            if (b & 1) {
              r = mod(r * a, N);
            }
          }
          return r;
        },
        "equals": function(a, b) {
          return a == b;
        }
      };
    }
  };

  if (typeof define === 'function' && define['amd']) {

    define(["fraction.js", "complex.js", "quaternion"], function(frac, comp, quat) {
      Fraction = frac;
      Complex = comp;
      Quaternion = quat;
      return Polynomial;
    });

  } else if (typeof exports === 'object') {

    Fraction = require("fraction.js");
    Complex = require("complex.js");
    Quaternion = require("quaternion");

    module['exports'] = Polynomial;

  } else {

    Fraction = root['Fraction'];
    Complex = root['Complex'];
    Quaternion = root['Quaternion'];

    root['Polynomial'] = Polynomial;
  }

})(this);
