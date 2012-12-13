// Copyright (c) 2005  Tom Wu
// All Rights Reserved.
// See "LICENSE" for details.

// Basic JavaScript BN library - subset useful for RSA encryption.

// Bits per digit
var dbits;

// JavaScript engine analysis
var canary = 0xdeadbeefcafe;
var j_lm = ((canary&0xffffff)==0xefcafe);

// (public) Constructor
function BigInteger(a,b,c) {
  if(a != null)
    if("number" == typeof a) this.fromNumber(a,b,c);
    else if(b == null && "string" != typeof a) this.fromString(a,256);
    else this.fromString(a,b);
}

// return new, unset BigInteger
function nbi() { return new BigInteger(null); }

// am: Compute w_j += (x*this_i), propagate carries,
// c is initial carry, returns final carry.
// c < 3*dvalue, x < 2*dvalue, this_i < dvalue
// We need to select the fastest one that works in this environment.

// am1: use a single mult and divide to get the high bits,
// max digit bits should be 26 because
// max internal value = 2*dvalue^2-2*dvalue (< 2^53)
function am1(i,x,w,j,c,n) {
  while(--n >= 0) {
    var v = x*this[i++]+w[j]+c;
    c = Math.floor(v/0x4000000);
    w[j++] = v&0x3ffffff;
  }
  return c;
}
// am2 avoids a big mult-and-extract completely.
// Max digit bits should be <= 30 because we do bitwise ops
// on values up to 2*hdvalue^2-hdvalue-1 (< 2^31)
function am2(i,x,w,j,c,n) {
  var xl = x&0x7fff, xh = x>>15;
  while(--n >= 0) {
    var l = this[i]&0x7fff;
    var h = this[i++]>>15;
    var m = xh*l+h*xl;
    l = xl*l+((m&0x7fff)<<15)+w[j]+(c&0x3fffffff);
    c = (l>>>30)+(m>>>15)+xh*h+(c>>>30);
    w[j++] = l&0x3fffffff;
  }
  return c;
}
// Alternately, set max digit bits to 28 since some
// browsers slow down when dealing with 32-bit numbers.
function am3(i,x,w,j,c,n) {
  var xl = x&0x3fff, xh = x>>14;
  while(--n >= 0) {
    var l = this[i]&0x3fff;
    var h = this[i++]>>14;
    var m = xh*l+h*xl;
    l = xl*l+((m&0x3fff)<<14)+w[j]+c;
    c = (l>>28)+(m>>14)+xh*h;
    w[j++] = l&0xfffffff;
  }
  return c;
}
if ( typeof navigator == 'object' ) {
  if(j_lm && (navigator.appName == "Microsoft Internet Explorer")) {
    BigInteger.prototype.am = am2;
    dbits = 30;
  }
  else if(j_lm && (navigator.appName != "Netscape")) {
    BigInteger.prototype.am = am1;
    dbits = 26;
  }
  else { // Mozilla/Netscape seems to prefer am3
    BigInteger.prototype.am = am3;
    dbits = 28;
  }
} else {
  BigInteger.prototype.am = am1;
  dbits = 26;
}

BigInteger.prototype.DB = dbits;
BigInteger.prototype.DM = ((1<<dbits)-1);
BigInteger.prototype.DV = (1<<dbits);

var BI_FP = 52;
BigInteger.prototype.FV = Math.pow(2,BI_FP);
BigInteger.prototype.F1 = BI_FP-dbits;
BigInteger.prototype.F2 = 2*dbits-BI_FP;

// Digit conversions
var BI_RM = "0123456789abcdefghijklmnopqrstuvwxyz";
var BI_RC = new Array();
var rr,vv;
rr = "0".charCodeAt(0);
for(vv = 0; vv <= 9; ++vv) BI_RC[rr++] = vv;
rr = "a".charCodeAt(0);
for(vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;
rr = "A".charCodeAt(0);
for(vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;

function int2char(n) { return BI_RM.charAt(n); }
function intAt(s,i) {
  var c = BI_RC[s.charCodeAt(i)];
  return (c==null)?-1:c;
}

// (protected) copy this to r
function bnpCopyTo(r) {
  for(var i = this.t-1; i >= 0; --i) r[i] = this[i];
  r.t = this.t;
  r.s = this.s;
}

// (protected) set from integer value x, -DV <= x < DV
function bnpFromInt(x) {
  this.t = 1;
  this.s = (x<0)?-1:0;
  if(x > 0) this[0] = x;
  else if(x < -1) this[0] = x+this.DV;
  else this.t = 0;
}

// return bigint initialized to value
function nbv(i) { var r = nbi(); r.fromInt(i); return r; }

// (protected) set from string and radix
function bnpFromString(s,b) {
  var k;
  if(b == 16) k = 4;
  else if(b == 8) k = 3;
  else if(b == 256) k = 8; // byte array
  else if(b == 2) k = 1;
  else if(b == 32) k = 5;
  else if(b == 4) k = 2;
  else { this.fromRadix(s,b); return; }
  this.t = 0;
  this.s = 0;
  var i = s.length, mi = false, sh = 0;
  while(--i >= 0) {
    var x = (k==8)?s[i]&0xff:intAt(s,i);
    if(x < 0) {
      if(s.charAt(i) == "-") mi = true;
      continue;
    }
    mi = false;
    if(sh == 0)
      this[this.t++] = x;
    else if(sh+k > this.DB) {
      this[this.t-1] |= (x&((1<<(this.DB-sh))-1))<<sh;
      this[this.t++] = (x>>(this.DB-sh));
    }
    else
      this[this.t-1] |= x<<sh;
    sh += k;
    if(sh >= this.DB) sh -= this.DB;
  }
  if(k == 8 && (s[0]&0x80) != 0) {
    this.s = -1;
    if(sh > 0) this[this.t-1] |= ((1<<(this.DB-sh))-1)<<sh;
  }
  this.clamp();
  if(mi) BigInteger.ZERO.subTo(this,this);
}

// (protected) clamp off excess high words
function bnpClamp() {
  var c = this.s&this.DM;
  while(this.t > 0 && this[this.t-1] == c) --this.t;
}

// (public) return string representation in given radix
function bnToString(b) {
  if(this.s < 0) return "-"+this.negate().toString(b);
  var k;
  if(b == 16) k = 4;
  else if(b == 8) k = 3;
  else if(b == 2) k = 1;
  else if(b == 32) k = 5;
  else if(b == 4) k = 2;
  else return this.toRadix(b);
  var km = (1<<k)-1, d, m = false, r = "", i = this.t;
  var p = this.DB-(i*this.DB)%k;
  if(i-- > 0) {
    if(p < this.DB && (d = this[i]>>p) > 0) { m = true; r = int2char(d); }
    while(i >= 0) {
      if(p < k) {
        d = (this[i]&((1<<p)-1))<<(k-p);
        d |= this[--i]>>(p+=this.DB-k);
      }
      else {
        d = (this[i]>>(p-=k))&km;
        if(p <= 0) { p += this.DB; --i; }
      }
      if(d > 0) m = true;
      if(m) r += int2char(d);
    }
  }
  return m?r:"0";
}

// (public) -this
function bnNegate() { var r = nbi(); BigInteger.ZERO.subTo(this,r); return r; }

// (public) |this|
function bnAbs() { return (this.s<0)?this.negate():this; }

// (public) return + if this > a, - if this < a, 0 if equal
function bnCompareTo(a) {
  var r = this.s-a.s;
  if(r != 0) return r;
  var i = this.t;
  r = i-a.t;
  if(r != 0) return r;
  while(--i >= 0) if((r=this[i]-a[i]) != 0) return r;
  return 0;
}

// returns bit length of the integer x
function nbits(x) {
  var r = 1, t;
  if((t=x>>>16) != 0) { x = t; r += 16; }
  if((t=x>>8) != 0) { x = t; r += 8; }
  if((t=x>>4) != 0) { x = t; r += 4; }
  if((t=x>>2) != 0) { x = t; r += 2; }
  if((t=x>>1) != 0) { x = t; r += 1; }
  return r;
}

// (public) return the number of bits in "this"
function bnBitLength() {
  if(this.t <= 0) return 0;
  return this.DB*(this.t-1)+nbits(this[this.t-1]^(this.s&this.DM));
}

// (protected) r = this << n*DB
function bnpDLShiftTo(n,r) {
  var i;
  for(i = this.t-1; i >= 0; --i) r[i+n] = this[i];
  for(i = n-1; i >= 0; --i) r[i] = 0;
  r.t = this.t+n;
  r.s = this.s;
}

// (protected) r = this >> n*DB
function bnpDRShiftTo(n,r) {
  for(var i = n; i < this.t; ++i) r[i-n] = this[i];
  r.t = Math.max(this.t-n,0);
  r.s = this.s;
}

// (protected) r = this << n
function bnpLShiftTo(n,r) {
  var bs = n%this.DB;
  var cbs = this.DB-bs;
  var bm = (1<<cbs)-1;
  var ds = Math.floor(n/this.DB), c = (this.s<<bs)&this.DM, i;
  for(i = this.t-1; i >= 0; --i) {
    r[i+ds+1] = (this[i]>>cbs)|c;
    c = (this[i]&bm)<<bs;
  }
  for(i = ds-1; i >= 0; --i) r[i] = 0;
  r[ds] = c;
  r.t = this.t+ds+1;
  r.s = this.s;
  r.clamp();
}

// (protected) r = this >> n
function bnpRShiftTo(n,r) {
  r.s = this.s;
  var ds = Math.floor(n/this.DB);
  if(ds >= this.t) { r.t = 0; return; }
  var bs = n%this.DB;
  var cbs = this.DB-bs;
  var bm = (1<<bs)-1;
  r[0] = this[ds]>>bs;
  for(var i = ds+1; i < this.t; ++i) {
    r[i-ds-1] |= (this[i]&bm)<<cbs;
    r[i-ds] = this[i]>>bs;
  }
  if(bs > 0) r[this.t-ds-1] |= (this.s&bm)<<cbs;
  r.t = this.t-ds;
  r.clamp();
}

// (protected) r = this - a
function bnpSubTo(a,r) {
  var i = 0, c = 0, m = Math.min(a.t,this.t);
  while(i < m) {
    c += this[i]-a[i];
    r[i++] = c&this.DM;
    c >>= this.DB;
  }
  if(a.t < this.t) {
    c -= a.s;
    while(i < this.t) {
      c += this[i];
      r[i++] = c&this.DM;
      c >>= this.DB;
    }
    c += this.s;
  }
  else {
    c += this.s;
    while(i < a.t) {
      c -= a[i];
      r[i++] = c&this.DM;
      c >>= this.DB;
    }
    c -= a.s;
  }
  r.s = (c<0)?-1:0;
  if(c < -1) r[i++] = this.DV+c;
  else if(c > 0) r[i++] = c;
  r.t = i;
  r.clamp();
}

// (protected) r = this * a, r != this,a (HAC 14.12)
// "this" should be the larger one if appropriate.
function bnpMultiplyTo(a,r) {
  var x = this.abs(), y = a.abs();
  var i = x.t;
  r.t = i+y.t;
  while(--i >= 0) r[i] = 0;
  for(i = 0; i < y.t; ++i) r[i+x.t] = x.am(0,y[i],r,i,0,x.t);
  r.s = 0;
  r.clamp();
  if(this.s != a.s) BigInteger.ZERO.subTo(r,r);
}

// (protected) r = this^2, r != this (HAC 14.16)
function bnpSquareTo(r) {
  var x = this.abs();
  var i = r.t = 2*x.t;
  while(--i >= 0) r[i] = 0;
  for(i = 0; i < x.t-1; ++i) {
    var c = x.am(i,x[i],r,2*i,0,1);
    if((r[i+x.t]+=x.am(i+1,2*x[i],r,2*i+1,c,x.t-i-1)) >= x.DV) {
      r[i+x.t] -= x.DV;
      r[i+x.t+1] = 1;
    }
  }
  if(r.t > 0) r[r.t-1] += x.am(i,x[i],r,2*i,0,1);
  r.s = 0;
  r.clamp();
}

// (protected) divide this by m, quotient and remainder to q, r (HAC 14.20)
// r != q, this != m.  q or r may be null.
function bnpDivRemTo(m,q,r) {
  var pm = m.abs();
  if(pm.t <= 0) return;
  var pt = this.abs();
  if(pt.t < pm.t) {
    if(q != null) q.fromInt(0);
    if(r != null) this.copyTo(r);
    return;
  }
  if(r == null) r = nbi();
  var y = nbi(), ts = this.s, ms = m.s;
  var nsh = this.DB-nbits(pm[pm.t-1]);	// normalize modulus
  if(nsh > 0) { pm.lShiftTo(nsh,y); pt.lShiftTo(nsh,r); }
  else { pm.copyTo(y); pt.copyTo(r); }
  var ys = y.t;
  var y0 = y[ys-1];
  if(y0 == 0) return;
  var yt = y0*(1<<this.F1)+((ys>1)?y[ys-2]>>this.F2:0);
  var d1 = this.FV/yt, d2 = (1<<this.F1)/yt, e = 1<<this.F2;
  var i = r.t, j = i-ys, t = (q==null)?nbi():q;
  y.dlShiftTo(j,t);
  if(r.compareTo(t) >= 0) {
    r[r.t++] = 1;
    r.subTo(t,r);
  }
  BigInteger.ONE.dlShiftTo(ys,t);
  t.subTo(y,y);	// "negative" y so we can replace sub with am later
  while(y.t < ys) y[y.t++] = 0;
  while(--j >= 0) {
    // Estimate quotient digit
    var qd = (r[--i]==y0)?this.DM:Math.floor(r[i]*d1+(r[i-1]+e)*d2);
    if((r[i]+=y.am(0,qd,r,j,0,ys)) < qd) {	// Try it out
      y.dlShiftTo(j,t);
      r.subTo(t,r);
      while(r[i] < --qd) r.subTo(t,r);
    }
  }
  if(q != null) {
    r.drShiftTo(ys,q);
    if(ts != ms) BigInteger.ZERO.subTo(q,q);
  }
  r.t = ys;
  r.clamp();
  if(nsh > 0) r.rShiftTo(nsh,r);	// Denormalize remainder
  if(ts < 0) BigInteger.ZERO.subTo(r,r);
}

// (public) this mod a
function bnMod(a) {
  var r = nbi();
  this.abs().divRemTo(a,null,r);
  if(this.s < 0 && r.compareTo(BigInteger.ZERO) > 0) a.subTo(r,r);
  return r;
}

// Modular reduction using "classic" algorithm
function Classic(m) { this.m = m; }
function cConvert(x) {
  if(x.s < 0 || x.compareTo(this.m) >= 0) return x.mod(this.m);
  else return x;
}
function cRevert(x) { return x; }
function cReduce(x) { x.divRemTo(this.m,null,x); }
function cMulTo(x,y,r) { x.multiplyTo(y,r); this.reduce(r); }
function cSqrTo(x,r) { x.squareTo(r); this.reduce(r); }

Classic.prototype.convert = cConvert;
Classic.prototype.revert = cRevert;
Classic.prototype.reduce = cReduce;
Classic.prototype.mulTo = cMulTo;
Classic.prototype.sqrTo = cSqrTo;

// (protected) return "-1/this % 2^DB"; useful for Mont. reduction
// justification:
//         xy == 1 (mod m)
//         xy =  1+km
//   xy(2-xy) = (1+km)(1-km)
// x[y(2-xy)] = 1-k^2m^2
// x[y(2-xy)] == 1 (mod m^2)
// if y is 1/x mod m, then y(2-xy) is 1/x mod m^2
// should reduce x and y(2-xy) by m^2 at each step to keep size bounded.
// JS multiply "overflows" differently from C/C++, so care is needed here.
function bnpInvDigit() {
  if(this.t < 1) return 0;
  var x = this[0];
  if((x&1) == 0) return 0;
  var y = x&3;		// y == 1/x mod 2^2
  y = (y*(2-(x&0xf)*y))&0xf;	// y == 1/x mod 2^4
  y = (y*(2-(x&0xff)*y))&0xff;	// y == 1/x mod 2^8
  y = (y*(2-(((x&0xffff)*y)&0xffff)))&0xffff;	// y == 1/x mod 2^16
  // last step - calculate inverse mod DV directly;
  // assumes 16 < DB <= 32 and assumes ability to handle 48-bit ints
  y = (y*(2-x*y%this.DV))%this.DV;		// y == 1/x mod 2^dbits
  // we really want the negative inverse, and -DV < y < DV
  return (y>0)?this.DV-y:-y;
}

// Montgomery reduction
function Montgomery(m) {
  this.m = m;
  this.mp = m.invDigit();
  this.mpl = this.mp&0x7fff;
  this.mph = this.mp>>15;
  this.um = (1<<(m.DB-15))-1;
  this.mt2 = 2*m.t;
}

// xR mod m
function montConvert(x) {
  var r = nbi();
  x.abs().dlShiftTo(this.m.t,r);
  r.divRemTo(this.m,null,r);
  if(x.s < 0 && r.compareTo(BigInteger.ZERO) > 0) this.m.subTo(r,r);
  return r;
}

// x/R mod m
function montRevert(x) {
  var r = nbi();
  x.copyTo(r);
  this.reduce(r);
  return r;
}

// x = x/R mod m (HAC 14.32)
function montReduce(x) {
  while(x.t <= this.mt2)	// pad x so am has enough room later
    x[x.t++] = 0;
  for(var i = 0; i < this.m.t; ++i) {
    // faster way of calculating u0 = x[i]*mp mod DV
    var j = x[i]&0x7fff;
    var u0 = (j*this.mpl+(((j*this.mph+(x[i]>>15)*this.mpl)&this.um)<<15))&x.DM;
    // use am to combine the multiply-shift-add into one call
    j = i+this.m.t;
    x[j] += this.m.am(0,u0,x,i,0,this.m.t);
    // propagate carry
    while(x[j] >= x.DV) { x[j] -= x.DV; x[++j]++; }
  }
  x.clamp();
  x.drShiftTo(this.m.t,x);
  if(x.compareTo(this.m) >= 0) x.subTo(this.m,x);
}

// r = "x^2/R mod m"; x != r
function montSqrTo(x,r) { x.squareTo(r); this.reduce(r); }

// r = "xy/R mod m"; x,y != r
function montMulTo(x,y,r) { x.multiplyTo(y,r); this.reduce(r); }

Montgomery.prototype.convert = montConvert;
Montgomery.prototype.revert = montRevert;
Montgomery.prototype.reduce = montReduce;
Montgomery.prototype.mulTo = montMulTo;
Montgomery.prototype.sqrTo = montSqrTo;

// (protected) true iff this is even
function bnpIsEven() { return ((this.t>0)?(this[0]&1):this.s) == 0; }

// (protected) this^e, e < 2^32, doing sqr and mul with "r" (HAC 14.79)
function bnpExp(e,z) {
  if(e > 0xffffffff || e < 1) return BigInteger.ONE;
  var r = nbi(), r2 = nbi(), g = z.convert(this), i = nbits(e)-1;
  g.copyTo(r);
  while(--i >= 0) {
    z.sqrTo(r,r2);
    if((e&(1<<i)) > 0) z.mulTo(r2,g,r);
    else { var t = r; r = r2; r2 = t; }
  }
  return z.revert(r);
}

// (public) this^e % m, 0 <= e < 2^32
function bnModPowInt(e,m) {
  var z;
  if(e < 256 || m.isEven()) z = new Classic(m); else z = new Montgomery(m);
  return this.exp(e,z);
}

// protected
BigInteger.prototype.copyTo = bnpCopyTo;
BigInteger.prototype.fromInt = bnpFromInt;
BigInteger.prototype.fromString = bnpFromString;
BigInteger.prototype.clamp = bnpClamp;
BigInteger.prototype.dlShiftTo = bnpDLShiftTo;
BigInteger.prototype.drShiftTo = bnpDRShiftTo;
BigInteger.prototype.lShiftTo = bnpLShiftTo;
BigInteger.prototype.rShiftTo = bnpRShiftTo;
BigInteger.prototype.subTo = bnpSubTo;
BigInteger.prototype.multiplyTo = bnpMultiplyTo;
BigInteger.prototype.squareTo = bnpSquareTo;
BigInteger.prototype.divRemTo = bnpDivRemTo;
BigInteger.prototype.invDigit = bnpInvDigit;
BigInteger.prototype.isEven = bnpIsEven;
BigInteger.prototype.exp = bnpExp;

// public
BigInteger.prototype.toString = bnToString;
BigInteger.prototype.negate = bnNegate;
BigInteger.prototype.abs = bnAbs;
BigInteger.prototype.compareTo = bnCompareTo;
BigInteger.prototype.bitLength = bnBitLength;
BigInteger.prototype.mod = bnMod;
BigInteger.prototype.modPowInt = bnModPowInt;

// "constants"
BigInteger.ZERO = nbv(0);
BigInteger.ONE = nbv(1);
// Copyright (c) 2005-2009  Tom Wu
// All Rights Reserved.
// See "LICENSE" for details.

// Extended JavaScript BN functions, required for RSA private ops.

// Version 1.1: new BigInteger("0", 10) returns "proper" zero

// (public)
function bnClone() { var r = nbi(); this.copyTo(r); return r; }

// (public) return value as integer
function bnIntValue() {
  if(this.s < 0) {
    if(this.t == 1) return this[0]-this.DV;
    else if(this.t == 0) return -1;
  }
  else if(this.t == 1) return this[0];
  else if(this.t == 0) return 0;
  // assumes 16 < DB < 32
  return ((this[1]&((1<<(32-this.DB))-1))<<this.DB)|this[0];
}

// (public) return value as double
function bnDoubleValue() {
  var x = this ;
  var sign = 1 ;
  if(x.s < 0) {
    x = x.negate() ;
    sign = -1 ;
  }
  var c = x.t - 1 ;
  var r = 0 ;
  while ( c >= 0 ) {
    r = r * x.DV + x[c];
    --c ;
  }
  return sign * r ;
}

// (public) return value as byte
function bnByteValue() { return (this.t==0)?this.s:(this[0]<<24)>>24; }

// (public) return value as short (assumes DB>=16)
function bnShortValue() { return (this.t==0)?this.s:(this[0]<<16)>>16; }

// (protected) return x s.t. r^x < DV
function bnpChunkSize(r) { return Math.floor(Math.LN2*this.DB/Math.log(r)); }

// (public) 0 if this == 0, 1 if this > 0
function bnSigNum() {
  if(this.s < 0) return -1;
  else if(this.t <= 0 || (this.t == 1 && this[0] <= 0)) return 0;
  else return 1;
}

// (protected) convert to radix string
function bnpToRadix(b) {
  if(b == null) b = 10;
  if(this.signum() == 0 || b < 2 || b > 36) return "0";
  var cs = this.chunkSize(b);
  var a = Math.pow(b,cs);
  var d = nbv(a), y = nbi(), z = nbi(), r = "";
  this.divRemTo(d,y,z);
  while(y.signum() > 0) {
    r = (a+z.intValue()).toString(b).substr(1) + r;
    y.divRemTo(d,y,z);
  }
  return z.intValue().toString(b) + r;
}

// (protected) convert from radix string
function bnpFromRadix(s,b) {
  this.fromInt(0);
  if(b == null) b = 10;
  var cs = this.chunkSize(b);
  var d = Math.pow(b,cs), mi = false, j = 0, w = 0;
  for(var i = 0; i < s.length; ++i) {
    var x = intAt(s,i);
    if(x < 0) {
      if(s.charAt(i) == "-" && this.signum() == 0) mi = true;
      continue;
    }
    w = b*w+x;
    if(++j >= cs) {
      this.dMultiply(d);
      this.dAddOffset(w,0);
      j = 0;
      w = 0;
    }
  }
  if(j > 0) {
    this.dMultiply(Math.pow(b,j));
    this.dAddOffset(w,0);
  }
  if(mi) BigInteger.ZERO.subTo(this,this);
}

// (protected) alternate constructor
function bnpFromDouble(x) {
  var sign = 1 ;
  var div = this.DV >> 1 ;
  if ( x < 0 ) {
    sign = -1 ;
    x = -x ;
  }
  var a = new Array() ;
  var c = 0 ;
  while( x > 0 ) {
    var d = Math.floor( x / div ) ;
    var r = x - d * div ;
    a[c] = r ;
    ++c ;
    // writeln("bnpFromDouble.L1 " + [x,d,r]) ;
    x = d ;
  }
  var n = nbv(0) ;
  for (c = a.length-1 ; c >= 0 ; --c ) {
    n.dMultiply(div) ;
    var x = nbv(a[c]) ;
    // writeln("bnpFromDouble.L2A " + [c,a[c],x,n]) ;
    n.addTo(x,n) ;
    // writeln("bnpFromDouble.L2B " + [c,a[c],x,r,n]) ;
  }
  if ( sign < 0 ) {
  	BigInteger.ZERO.subTo(n,this) ;
  } else {
    n.copyTo(this) ;
  }
}

// (protected) alternate constructor
function bnpFromNumber(a,b,c) {
  if("number" == typeof b) {
    // new BigInteger(int,int,RNG)
    if(a < 2) this.fromInt(1);
    else {
      this.fromNumber(a,c);
      if(!this.testBit(a-1))	// force MSB set
        this.bitwiseTo(BigInteger.ONE.shiftLeft(a-1),op_or,this);
      if(this.isEven()) this.dAddOffset(1,0); // force odd
      while(!this.isProbablePrime(b)) {
        this.dAddOffset(2,0);
        if(this.bitLength() > a) this.subTo(BigInteger.ONE.shiftLeft(a-1),this);
      }
    }
  }
  else {
    // new BigInteger(int,RNG)
    var x = new Array(), t = a&7;
    x.length = (a>>3)+1;
    b.nextBytes(x);
    if(t > 0) x[0] &= ((1<<t)-1); else x[0] = 0;
    this.fromString(x,256);
  }
}

// (public) convert to bigendian byte array
function bnToByteArray() {
  var i = this.t, r = new Array();
  r[0] = this.s;
  var p = this.DB-(i*this.DB)%8, d, k = 0;
  if(i-- > 0) {
    if(p < this.DB && (d = this[i]>>p) != (this.s&this.DM)>>p)
      r[k++] = d|(this.s<<(this.DB-p));
    while(i >= 0) {
      if(p < 8) {
        d = (this[i]&((1<<p)-1))<<(8-p);
        d |= this[--i]>>(p+=this.DB-8);
      }
      else {
        d = (this[i]>>(p-=8))&0xff;
        if(p <= 0) { p += this.DB; --i; }
      }
      if((d&0x80) != 0) d |= -256;
      if(k == 0 && (this.s&0x80) != (d&0x80)) ++k;
      if(k > 0 || d != this.s) r[k++] = d;
    }
  }
  return r;
}

function bnEquals(a) { return(this.compareTo(a)==0); }
function bnMin(a) { return(this.compareTo(a)<0)?this:a; }
function bnMax(a) { return(this.compareTo(a)>0)?this:a; }

// (protected) r = this op a (bitwise)
function bnpBitwiseTo(a,op,r) {
  var i, f, m = Math.min(a.t,this.t);
  for(i = 0; i < m; ++i) r[i] = op(this[i],a[i]);
  if(a.t < this.t) {
    f = a.s&this.DM;
    for(i = m; i < this.t; ++i) r[i] = op(this[i],f);
    r.t = this.t;
  }
  else {
    f = this.s&this.DM;
    for(i = m; i < a.t; ++i) r[i] = op(f,a[i]);
    r.t = a.t;
  }
  r.s = op(this.s,a.s);
  r.clamp();
}

// (public) this & a
function op_and(x,y) { return x&y; }
function bnAnd(a) { var r = nbi(); this.bitwiseTo(a,op_and,r); return r; }

// (public) this | a
function op_or(x,y) { return x|y; }
function bnOr(a) { var r = nbi(); this.bitwiseTo(a,op_or,r); return r; }

// (public) this ^ a
function op_xor(x,y) { return x^y; }
function bnXor(a) { var r = nbi(); this.bitwiseTo(a,op_xor,r); return r; }

// (public) this & ~a
function op_andnot(x,y) { return x&~y; }
function bnAndNot(a) { var r = nbi(); this.bitwiseTo(a,op_andnot,r); return r; }

// (public) ~this
function bnNot() {
  var r = nbi();
  for(var i = 0; i < this.t; ++i) r[i] = this.DM&~this[i];
  r.t = this.t;
  r.s = ~this.s;
  return r;
}

// (public) this << n
function bnShiftLeft(n) {
  var r = nbi();
  if(n < 0) this.rShiftTo(-n,r); else this.lShiftTo(n,r);
  return r;
}

// (public) this >> n
function bnShiftRight(n) {
  var r = nbi();
  if(n < 0) this.lShiftTo(-n,r); else this.rShiftTo(n,r);
  return r;
}

// return index of lowest 1-bit in x, x < 2^31
function lbit(x) {
  if(x == 0) return -1;
  var r = 0;
  if((x&0xffff) == 0) { x >>= 16; r += 16; }
  if((x&0xff) == 0) { x >>= 8; r += 8; }
  if((x&0xf) == 0) { x >>= 4; r += 4; }
  if((x&3) == 0) { x >>= 2; r += 2; }
  if((x&1) == 0) ++r;
  return r;
}

// (public) returns index of lowest 1-bit (or -1 if none)
function bnGetLowestSetBit() {
  for(var i = 0; i < this.t; ++i)
    if(this[i] != 0) return i*this.DB+lbit(this[i]);
  if(this.s < 0) return this.t*this.DB;
  return -1;
}

// return number of 1 bits in x
function cbit(x) {
  var r = 0;
  while(x != 0) { x &= x-1; ++r; }
  return r;
}

// (public) return number of set bits
function bnBitCount() {
  var r = 0, x = this.s&this.DM;
  for(var i = 0; i < this.t; ++i) r += cbit(this[i]^x);
  return r;
}

// (public) true iff nth bit is set
function bnTestBit(n) {
  var j = Math.floor(n/this.DB);
  if(j >= this.t) return(this.s!=0);
  return((this[j]&(1<<(n%this.DB)))!=0);
}

// (protected) this op (1<<n)
function bnpChangeBit(n,op) {
  var r = BigInteger.ONE.shiftLeft(n);
  this.bitwiseTo(r,op,r);
  return r;
}

// (public) this | (1<<n)
function bnSetBit(n) { return this.changeBit(n,op_or); }

// (public) this & ~(1<<n)
function bnClearBit(n) { return this.changeBit(n,op_andnot); }

// (public) this ^ (1<<n)
function bnFlipBit(n) { return this.changeBit(n,op_xor); }

// (protected) r = this + a
function bnpAddTo(a,r) {
  var i = 0, c = 0, m = Math.min(a.t,this.t);
  while(i < m) {
    c += this[i]+a[i];
    r[i++] = c&this.DM;
    c >>= this.DB;
  }
  if(a.t < this.t) {
    c += a.s;
    while(i < this.t) {
      c += this[i];
      r[i++] = c&this.DM;
      c >>= this.DB;
    }
    c += this.s;
  }
  else {
    c += this.s;
    while(i < a.t) {
      c += a[i];
      r[i++] = c&this.DM;
      c >>= this.DB;
    }
    c += a.s;
  }
  r.s = (c<0)?-1:0;
  if(c > 0) r[i++] = c;
  else if(c < -1) r[i++] = this.DV+c;
  r.t = i;
  r.clamp();
}

// (public) this + a
function bnAdd(a) { var r = nbi(); this.addTo(a,r); return r; }

// (public) this - a
function bnSubtract(a) { var r = nbi(); this.subTo(a,r); return r; }

// (public) this * a
function bnMultiply(a) { var r = nbi(); this.multiplyTo(a,r); return r; }

// (public) this / a
function bnDivide(a) { var r = nbi(); this.divRemTo(a,r,null); return r; }

// (public) this % a
function bnRemainder(a) { var r = nbi(); this.divRemTo(a,null,r); return r; }

// (public) [this/a,this%a]
function bnDivideAndRemainder(a) {
  var q = nbi(), r = nbi();
  this.divRemTo(a,q,r);
  return new Array(q,r);
}

// (protected) this *= n, this >= 0, 1 < n < DV
function bnpDMultiply(n) {
  this[this.t] = this.am(0,n-1,this,0,0,this.t);
  ++this.t;
  this.clamp();
}

// (protected) this += n << w words, this >= 0
function bnpDAddOffset(n,w) {
  if(n == 0) return;
  while(this.t <= w) this[this.t++] = 0;
  this[w] += n;
  while(this[w] >= this.DV) {
    this[w] -= this.DV;
    if(++w >= this.t) this[this.t++] = 0;
    ++this[w];
  }
}

// A "null" reducer
function NullExp() {}
function nNop(x) { return x; }
function nMulTo(x,y,r) { x.multiplyTo(y,r); }
function nSqrTo(x,r) { x.squareTo(r); }

NullExp.prototype.convert = nNop;
NullExp.prototype.revert = nNop;
NullExp.prototype.mulTo = nMulTo;
NullExp.prototype.sqrTo = nSqrTo;

// (public) this^e
function bnPow(e) { return this.exp(e,new NullExp()); }

// (protected) r = lower n words of "this * a", a.t <= n
// "this" should be the larger one if appropriate.
function bnpMultiplyLowerTo(a,n,r) {
  var i = Math.min(this.t+a.t,n);
  r.s = 0; // assumes a,this >= 0
  r.t = i;
  while(i > 0) r[--i] = 0;
  var j;
  for(j = r.t-this.t; i < j; ++i) r[i+this.t] = this.am(0,a[i],r,i,0,this.t);
  for(j = Math.min(a.t,n); i < j; ++i) this.am(0,a[i],r,i,0,n-i);
  r.clamp();
}

// (protected) r = "this * a" without lower n words, n > 0
// "this" should be the larger one if appropriate.
function bnpMultiplyUpperTo(a,n,r) {
  --n;
  var i = r.t = this.t+a.t-n;
  r.s = 0; // assumes a,this >= 0
  while(--i >= 0) r[i] = 0;
  for(i = Math.max(n-this.t,0); i < a.t; ++i)
    r[this.t+i-n] = this.am(n-i,a[i],r,0,0,this.t+i-n);
  r.clamp();
  r.drShiftTo(1,r);
}

// Barrett modular reduction
function Barrett(m) {
  // setup Barrett
  this.r2 = nbi();
  this.q3 = nbi();
  BigInteger.ONE.dlShiftTo(2*m.t,this.r2);
  this.mu = this.r2.divide(m);
  this.m = m;
}

function barrettConvert(x) {
  if(x.s < 0 || x.t > 2*this.m.t) return x.mod(this.m);
  else if(x.compareTo(this.m) < 0) return x;
  else { var r = nbi(); x.copyTo(r); this.reduce(r); return r; }
}

function barrettRevert(x) { return x; }

// x = x mod m (HAC 14.42)
function barrettReduce(x) {
  x.drShiftTo(this.m.t-1,this.r2);
  if(x.t > this.m.t+1) { x.t = this.m.t+1; x.clamp(); }
  this.mu.multiplyUpperTo(this.r2,this.m.t+1,this.q3);
  this.m.multiplyLowerTo(this.q3,this.m.t+1,this.r2);
  while(x.compareTo(this.r2) < 0) x.dAddOffset(1,this.m.t+1);
  x.subTo(this.r2,x);
  while(x.compareTo(this.m) >= 0) x.subTo(this.m,x);
}

// r = x^2 mod m; x != r
function barrettSqrTo(x,r) { x.squareTo(r); this.reduce(r); }

// r = x*y mod m; x,y != r
function barrettMulTo(x,y,r) { x.multiplyTo(y,r); this.reduce(r); }

Barrett.prototype.convert = barrettConvert;
Barrett.prototype.revert = barrettRevert;
Barrett.prototype.reduce = barrettReduce;
Barrett.prototype.mulTo = barrettMulTo;
Barrett.prototype.sqrTo = barrettSqrTo;

// (public) this^e % m (HAC 14.85)
function bnModPow(e,m) {
  var i = e.bitLength(), k, r = nbv(1), z;
  if(i <= 0) return r;
  else if(i < 18) k = 1;
  else if(i < 48) k = 3;
  else if(i < 144) k = 4;
  else if(i < 768) k = 5;
  else k = 6;
  if(i < 8)
    z = new Classic(m);
  else if(m.isEven())
    z = new Barrett(m);
  else
    z = new Montgomery(m);

  // precomputation
  var g = new Array(), n = 3, k1 = k-1, km = (1<<k)-1;
  g[1] = z.convert(this);
  if(k > 1) {
    var g2 = nbi();
    z.sqrTo(g[1],g2);
    while(n <= km) {
      g[n] = nbi();
      z.mulTo(g2,g[n-2],g[n]);
      n += 2;
    }
  }

  var j = e.t-1, w, is1 = true, r2 = nbi(), t;
  i = nbits(e[j])-1;
  while(j >= 0) {
    if(i >= k1) w = (e[j]>>(i-k1))&km;
    else {
      w = (e[j]&((1<<(i+1))-1))<<(k1-i);
      if(j > 0) w |= e[j-1]>>(this.DB+i-k1);
    }

    n = k;
    while((w&1) == 0) { w >>= 1; --n; }
    if((i -= n) < 0) { i += this.DB; --j; }
    if(is1) {	// ret == 1, don't bother squaring or multiplying it
      g[w].copyTo(r);
      is1 = false;
    }
    else {
      while(n > 1) { z.sqrTo(r,r2); z.sqrTo(r2,r); n -= 2; }
      if(n > 0) z.sqrTo(r,r2); else { t = r; r = r2; r2 = t; }
      z.mulTo(r2,g[w],r);
    }

    while(j >= 0 && (e[j]&(1<<i)) == 0) {
      z.sqrTo(r,r2); t = r; r = r2; r2 = t;
      if(--i < 0) { i = this.DB-1; --j; }
    }
  }
  return z.revert(r);
}

// (public) gcd(this,a) (HAC 14.54)
function bnGCD(a) {
  var x = (this.s<0)?this.negate():this.clone();
  var y = (a.s<0)?a.negate():a.clone();
  if(x.compareTo(y) < 0) { var t = x; x = y; y = t; }
  var i = x.getLowestSetBit(), g = y.getLowestSetBit();
  if(g < 0) return x;
  if(i < g) g = i;
  if(g > 0) {
    x.rShiftTo(g,x);
    y.rShiftTo(g,y);
  }
  while(x.signum() > 0) {
    if((i = x.getLowestSetBit()) > 0) x.rShiftTo(i,x);
    if((i = y.getLowestSetBit()) > 0) y.rShiftTo(i,y);
    if(x.compareTo(y) >= 0) {
      x.subTo(y,x);
      x.rShiftTo(1,x);
    }
    else {
      y.subTo(x,y);
      y.rShiftTo(1,y);
    }
  }
  if(g > 0) y.lShiftTo(g,y);
  return y;
}

// (protected) this % n, n < 2^26
function bnpModInt(n) {
  if(n <= 0) return 0;
  var d = this.DV%n, r = (this.s<0)?n-1:0;
  if(this.t > 0)
    if(d == 0) r = this[0]%n;
    else for(var i = this.t-1; i >= 0; --i) r = (d*r+this[i])%n;
  return r;
}

// (public) 1/this % m (HAC 14.61)
function bnModInverse(m) {
  var ac = m.isEven();
  if((this.isEven() && ac) || m.signum() == 0) return BigInteger.ZERO;
  var u = m.clone(), v = this.clone();
  var a = nbv(1), b = nbv(0), c = nbv(0), d = nbv(1);
  while(u.signum() != 0) {
    while(u.isEven()) {
      u.rShiftTo(1,u);
      if(ac) {
        if(!a.isEven() || !b.isEven()) { a.addTo(this,a); b.subTo(m,b); }
        a.rShiftTo(1,a);
      }
      else if(!b.isEven()) b.subTo(m,b);
      b.rShiftTo(1,b);
    }
    while(v.isEven()) {
      v.rShiftTo(1,v);
      if(ac) {
        if(!c.isEven() || !d.isEven()) { c.addTo(this,c); d.subTo(m,d); }
        c.rShiftTo(1,c);
      }
      else if(!d.isEven()) d.subTo(m,d);
      d.rShiftTo(1,d);
    }
    if(u.compareTo(v) >= 0) {
      u.subTo(v,u);
      if(ac) a.subTo(c,a);
      b.subTo(d,b);
    }
    else {
      v.subTo(u,v);
      if(ac) c.subTo(a,c);
      d.subTo(b,d);
    }
  }
  if(v.compareTo(BigInteger.ONE) != 0) return BigInteger.ZERO;
  if(d.compareTo(m) >= 0) return d.subtract(m);
  if(d.signum() < 0) d.addTo(m,d); else return d;
  if(d.signum() < 0) return d.add(m); else return d;
}

var lowprimes = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509];
var lplim = (1<<26)/lowprimes[lowprimes.length-1];

// (public) test primality with certainty >= 1-.5^t
function bnIsProbablePrime(t) {
  var i, x = this.abs();
  if(x.t == 1 && x[0] <= lowprimes[lowprimes.length-1]) {
    for(i = 0; i < lowprimes.length; ++i)
      if(x[0] == lowprimes[i]) return true;
    return false;
  }
  if(x.isEven()) return false;
  i = 1;
  while(i < lowprimes.length) {
    var m = lowprimes[i], j = i+1;
    while(j < lowprimes.length && m < lplim) m *= lowprimes[j++];
    m = x.modInt(m);
    while(i < j) if(m%lowprimes[i++] == 0) return false;
  }
  return x.millerRabin(t);
}

// (protected) true if probably prime (HAC 4.24, Miller-Rabin)
function bnpMillerRabin(t) {
  var n1 = this.subtract(BigInteger.ONE);
  var k = n1.getLowestSetBit();
  if(k <= 0) return false;
  var r = n1.shiftRight(k);
  t = (t+1)>>1;
  if(t > lowprimes.length) t = lowprimes.length;
  var a = nbi();
  for(var i = 0; i < t; ++i) {
    a.fromInt(lowprimes[i]);
    var y = a.modPow(r,this);
    if(y.compareTo(BigInteger.ONE) != 0 && y.compareTo(n1) != 0) {
      var j = 1;
      while(j++ < k && y.compareTo(n1) != 0) {
        y = y.modPowInt(2,this);
        if(y.compareTo(BigInteger.ONE) == 0) return false;
      }
      if(y.compareTo(n1) != 0) return false;
    }
  }
  return true;
}

// protected
BigInteger.prototype.chunkSize = bnpChunkSize;
BigInteger.prototype.toRadix = bnpToRadix;
BigInteger.prototype.fromRadix = bnpFromRadix;
BigInteger.prototype.fromDouble = bnpFromDouble;
BigInteger.prototype.fromNumber = bnpFromNumber;
BigInteger.prototype.bitwiseTo = bnpBitwiseTo;
BigInteger.prototype.changeBit = bnpChangeBit;
BigInteger.prototype.addTo = bnpAddTo;
BigInteger.prototype.dMultiply = bnpDMultiply;
BigInteger.prototype.dAddOffset = bnpDAddOffset;
BigInteger.prototype.multiplyLowerTo = bnpMultiplyLowerTo;
BigInteger.prototype.multiplyUpperTo = bnpMultiplyUpperTo;
BigInteger.prototype.modInt = bnpModInt;
BigInteger.prototype.millerRabin = bnpMillerRabin;

// public
BigInteger.prototype.clone = bnClone;
BigInteger.prototype.intValue = bnIntValue;
BigInteger.prototype.byteValue = bnByteValue;
BigInteger.prototype.shortValue = bnShortValue;
BigInteger.prototype.doubleValue = bnDoubleValue;
BigInteger.prototype.signum = bnSigNum;
BigInteger.prototype.toByteArray = bnToByteArray;
BigInteger.prototype.equals = bnEquals;
BigInteger.prototype.min = bnMin;
BigInteger.prototype.max = bnMax;
BigInteger.prototype.and = bnAnd;
BigInteger.prototype.or = bnOr;
BigInteger.prototype.xor = bnXor;
BigInteger.prototype.andNot = bnAndNot;
BigInteger.prototype.not = bnNot;
BigInteger.prototype.shiftLeft = bnShiftLeft;
BigInteger.prototype.shiftRight = bnShiftRight;
BigInteger.prototype.getLowestSetBit = bnGetLowestSetBit;
BigInteger.prototype.bitCount = bnBitCount;
BigInteger.prototype.testBit = bnTestBit;
BigInteger.prototype.setBit = bnSetBit;
BigInteger.prototype.clearBit = bnClearBit;
BigInteger.prototype.flipBit = bnFlipBit;
BigInteger.prototype.add = bnAdd;
BigInteger.prototype.subtract = bnSubtract;
BigInteger.prototype.multiply = bnMultiply;
BigInteger.prototype.divide = bnDivide;
BigInteger.prototype.remainder = bnRemainder;
BigInteger.prototype.divideAndRemainder = bnDivideAndRemainder;
BigInteger.prototype.modPow = bnModPow;
BigInteger.prototype.modInverse = bnModInverse;
BigInteger.prototype.pow = bnPow;
BigInteger.prototype.gcd = bnGCD;
BigInteger.prototype.isProbablePrime = bnIsProbablePrime;

// BigInteger interfaces not implemented in jsbn:

// BigInteger(int signum, byte[] magnitude)
// double doubleValue()
// float floatValue()
// int hashCode()
// long longValue()
// static BigInteger valueOf(long val)

// interface to eval
function _e_(x) {
  var x_, xx, x_next;
  if (x !== undefined && x !== null && x.__eOrV__ !== undefined) {
    x_ = x;
    do {
      if (typeof x.__eOrV__ === 'function' && !x.fe) {
        xx = x.__eOrV__();
        x.__eOrV__ = xx;
        x = xx;
      } else {
        x = x.__eOrV__;
      }
    } while (x !== undefined && x !== null && x.__eOrV__ !== undefined);
    while (x_ !== undefined && x_ !== null && x_.__eOrV__ !== undefined) {
      x_next = x_.__eOrV__;
      x_.__eOrV__ = x;
      x_.fe = true;
      x_ = x_next;
    }
  }
  return x;
}

function _A_undersat_(fun, args) {
  // this.needs = fun.needs - args.length;
  this.fun = fun;
  this.args = args;
}

// Apply node, not enough args
_A_undersat_.prototype = {
  __aN__ : function (args) {
    var needs, fun;
    needs = this.needsNrArgs();
    if (args.length < needs) {
      return new _A_undersat_(this, args);
    } else if (args.length === needs) {
      return this.fun.__aN__(this.args.concat(args));
    } else {
      fun = _e_(this.__aN__(args.slice(0, needs)));
      return {
        __eOrV__ : function () {
          return fun.__aN__(args.slice(needs));
        }
      };
    }
  },
  needsNrArgs : function () {
    return this.fun.needsNrArgs() - this.args.length;
  },
};

// Apply node, unknown how much is missing or too much
_A_.prototype = {
  __aN__ : function (args) {
    var fun = _e_(this);
    return {
      __eOrV__ : function () {
        return fun.__aN__(args);
      }
    };
  },
};
function _A_(fun, args) {
  this.__eOrV__ = function () {
    var x = fun.__aN__(args);
    return x;
  };
  this.fe = false;
}

function _F_(evalN) {
  //this.needs = evalN.length;
  this.__evN__ = evalN;
}

// Function node
_F_.prototype = {
  __aN__ : function (args) {
    var x, fun, remargs;
    if (args.length < this.__evN__.length) {
      return new _A_undersat_(this, args);
    } else if (args.length === this.__evN__.length) {
      x = this.__evN__.apply(null, args);
      return x;
    } else {
      fun = _e_(this.__evN__.apply(null, args.slice(0, this.__evN__.length)));
      remargs = args.slice(this.__evN__.length);
      return {
        __eOrV__ : function () {
          return fun.__aN__(remargs);
        }
      };
    }
  },
  needsNrArgs : function () {
    return this.__evN__.length;
  },
}

// lazy application wrappers
function _a0_(f) {
  return new _A_(f, []);
}

// indirection
function _i_() {
  return new _A_(new _F_(
    function () {throw "_i_: attempt to prematurely evaluate indirection"; }
  ), []);
}

function _i_set_(i, x) {
  i.__eOrV__ = x;
}

if (typeof document !== 'object') {
  document = {
    write   : function (x) {return write(x); },
    writeln : function (x) {return writeln(x); }
  };
};

PrimDataOrdering_EQ = {_tag_ : 0}
PrimDataOrdering_GT = {_tag_ : 1}
PrimDataOrdering_LT = {_tag_ : 2}

PrimDataBool_False = {_tag_ : 0}
PrimDataBool_True  = {_tag_ : 1}

PrimDataList_Nil = {_tag_ : 1}
PrimDataList_Cons  = {_tag_ : 0}

PrimMkBool = function(x) {
  return ( (x) ? PrimDataBool_True : PrimDataBool_False ) ;
}

// signed, int
primAddInt = function(x,y) {
  return x+y ;
}
primSubInt = function(x,y) {
  return x-y ;
}
primMulInt = function(x,y) {
  return x*y ;
}

// primDivInt = function(x,y) {var r = primQuotInt(x,y) ; return ( (r<0) ? r-1 : r ) ;}
primDivInt = function(x,y) {
  return Math.floor(x/y) ;
}
primModInt = function(x,y) {
  var r = x%y ;
  return ( (r > 0 && y < 0 || r < 0 && y > 0) ? r+y : r ) ;
}
primDivModInt = function(x,y) {
  return [primDivInt (x,y), primModInt(x,y)] ;
}

// primQuotInt = function(x,y) {return Math.floor(x/y) ;}
primQuotInt = function(x,y) {
  var r = primDivInt(x,y) ;
  return ( (r<0) ? r+1 : r ) ;
}
primRemInt = function(x,y) {
  return x%y ;
}
primQuotRemInt = function(x,y) {
  return [primQuotInt(x,y), x%y] ;
}

primNegInt = function(x) {
  return -x ;
}
primComplementInt = function(x) {
  return ~x ;
}

primShiftLeftInt  = function(x,y) {
  return x<<y ;
}
primShiftRightInt = function(x,y) {
  return x>>y ;
}

primRotateLeftInt  = function(x,y) {
  var s = (x<0 ? -1 : 1) ;
  x=x*s ;
  return s * ((x << y) | (x >> (31 - y))) ;
}
primRotateRightInt = function(x,y) {
  var s = (x<0 ? -1 : 1) ;
  x=x*s ;
  return s * ((x >> y) | (x << (31 - y))) ;
}

primEqInt = function(x,y) {
  return PrimMkBool(x==y) ;
}
primNeInt = function(x,y) {
  return PrimMkBool(x!=y) ;
}
primLtInt = function(x,y) {
  return PrimMkBool(x< y) ;
}
primGtInt = function(x,y) {
  return PrimMkBool(x> y) ;
}
primLeInt = function(x,y) {
  return PrimMkBool(x<=y) ;
}
primGeInt = function(x,y) {
  return PrimMkBool(x>=y) ;
}

primCmpInt = function(x,y) {
  return ( (x>y) ? PrimDataOrdering_GT : ( (x<y) ? PrimDataOrdering_LT : PrimDataOrdering_EQ ) ) ;
}

/*
primMinInt = function() {return -(1<<31) ;}
primMaxInt = function() {return (1<<31)-1 ;}
*/
primMinInt = function() {return -(1<<30) ;}
primMaxInt = function() {return (1<<30)-1 ;}

primUnsafeId = function(x) {
  return x ;
}

primIntegerToInt = function(x) {
  return x.intValue() ;
}
primIntToInteger = function(x) {
  var r = nbi();
  r.fromDouble(x);
  return r;
}
// primIntToInteger = nbv ;

primAndInt = function(x,y) {
  return x&y ;
}
primOrInt  = function(x,y) {
  return x|y ;
}
primXorInt = function(x,y) {
  return x^y ;
}

// Integer
primEqInteger = function(x,y) {
  return PrimMkBool(x.compareTo(y) == 0) ;
}
primNeInteger = function(x,y) {
  return PrimMkBool(x.compareTo(y) != 0) ;
}
primLtInteger = function(x,y) {
  return PrimMkBool(x.compareTo(y) <  0) ;
}
primGtInteger = function(x,y) {
  return PrimMkBool(x.compareTo(y) >  0) ;
}
primLeInteger = function(x,y) {
  return PrimMkBool(x.compareTo(y) <= 0) ;
}
primGeInteger = function(x,y) {
  return PrimMkBool(x.compareTo(y) >= 0) ;
}

primCmpInteger = function(x,y) {
  var c=x.compareTo(y) ;
  return ( (c>0) ? PrimDataOrdering_GT : ( (c<0) ? PrimDataOrdering_LT : PrimDataOrdering_EQ ) ) ;
}
primQuotRemInteger = function(x,y) {
  var q = nbi() ;
  var r = nbi() ;
  x.divRemTo(y,q,r) ;
  return [q,r] ;
}

primDivInteger = function(  v1,  v2 ) {
	var r = v1.divide(v2) ;
	if ( r.signum() < 0 )
		return r.subtract( BigInteger.ONE ) ;
	return r ;
}
primModInteger = function(  v1,  v2 ) {
	return ( v2.signum() < 0 ? v1.mod(v2.negate()).add(v2) : v1.mod(v2) ) ;
}
primDivModInteger = function(x,y) {
  return [primDivInteger (x,y), primModInteger(x,y)] ;
}

primAndInteger = function(x,y) {
  return x.and(y) ;
}
primOrInteger  = function(x,y) {
  return x.or(y) ;
}
primXorInteger = function(x,y) {
  return x.xor(y) ;
}

primComplementInteger = function(x) {
  return x.not() ;
}

primShiftLeftInteger = function(x,y) {
  return x.shiftLeft(y) ;
}
primShiftRightInteger = function(x,y) {
  return x.shiftRight(y) ;
}

primRotateLeftWord  = function(x,y) {
  return (x << y) | (x >> (32 - y)) ;
}
primRotateRightWord = function(x,y) {
  return (x >> y) | (x << (32 - y)) ;
}

primComplementWord = primComplementInt ;

// unsigned specific
primMinWord = function() {return 0 ;}
primMaxWord = function() {return (1<<32)-1 ;}

primAndWord = primAndInt ;
primOrWord  = primOrInt  ;
primXorWord = primXorInt ;

primShiftLeftWord  = primShiftLeftInt  ;
primShiftRightWord = primShiftRightInt ;

/// TODO: sign
primIntegerToWord = primIntegerToInt ;

// float, double
primDivideDouble = function(x,y) {
  return x/y ;
}
primRecipDouble = function(x) {
  return 1/x ;
}
primRationalToDouble = function(x) {
  var e1 = _e_(x._1);
  var e2 = _e_(x._2);
  return e1.doubleValue() / e2.doubleValue() ;
}

primSinDouble  = function(x) {
  return Math.sin(x) ;
}
primCosDouble  = function(x) {
  return Math.cos(x) ;
}
primTanDouble  = function(x) {
  return Math.tan(x) ;
}
primAsinDouble = function(x) {
  return Math.asin(x) ;
}
primAcosDouble = function(x) {
  return Math.acos(x) ;
}
primAtanDouble = function(x) {
  return Math.atan(x) ;
}
primExpDouble  = function(x) {
  return Math.exp(x) ;
}
primLogDouble  = function(x) {
  return Math.log(x) ;
}
primSqrtDouble = function(x) {
  return Math.sqrt(x) ;
}
primSinhDouble = function(x) {
  return (Math.exp(x) - Math.exp(-x))/2 ;
}
primCoshDouble = function(x) {
  return (Math.exp(x) + Math.exp(-x))/2 ;
}
primTanhDouble = function(x) {
  return primSinhDouble(x) / primCoshDouble(x) ;
}

primAtan2Double = function(x,y) {
  return Math.atan2(x,y) ;
}



primCharIsUpper = function(x) {
  return PrimMkBool(x > 64 && x < 91 ) ;
}
primCharIsLower = function(x) {
  return PrimMkBool(x > 96 && x < 123) ;
}
primCharToLower = function(charCode) {
  return String.fromCharCode(charCode).toLowerCase().charCodeAt(0);
};
primCharToUpper = function(charCode) {
  return String.fromCharCode(charCode).toUpperCase().charCodeAt(0);
};

primPackedStringNull = function(x) {
  return PrimMkBool(x.length == 0) ;
}
primPackedStringHead = function(x) {
  return x.charCodeAt(0) ;
}
primPackedStringTail = function(x) {
  return x.slice(1) ;
}
// primPackedStringToInteger = function(x) { return parseInt(x) ; }
primPackedStringToInteger = function(x) {
  return new BigInteger(x,10);
}
primStringToPackedString = function(l) {
	var pos = 0 ;
	var a = new Array() ;
	while (l._tag_ != PrimDataList_Nil._tag_) {
		a[pos] = _e_(l._1) ;
		++pos ;
		l = _e_(l._2) ;
	}
	return String.fromCharCode.apply(null,a) ;
}

primNewArray = function(len,x) {
	var a = new Array() ;
	for (var i = 0 ; i < len ; i++ ) {
		a[i] = x ;
	}
	return a ;
}
primIndexArray = function(a,i) { return a[i] ; }
primWriteArray = function(a,i,x) { a[i] = x ; return [] ; }
primSameArray = function(x,y) { return PrimMkBool(x===y) ; }

primByteArrayLength = function(x) { return x.length ; }
primByteArrayToPackedString = primUnsafeId ;

// primThrowException :: forall a x . SomeException' x -> a
primThrowException = function(x) { throw x ; }

primExitWith = function(x) { throw "EXIT:" + x ; }

// primCatchException :: forall a . a -> (SomeException -> a) -> a
primCatchException = function(x,hdlr) {
	try {
		return _e_(x);
	} catch (err) {
		return _e_(new _A_(hdlr,[err]));
	}
}

// primShowIntegerToPackedString = function(x) { return x.toString() ; }

primShowDoubleToPackedString = function(x) {
  return x.toString() ;
}
primShowFloatToPackedString = primShowDoubleToPackedString ;

// TODO:
// primShowDoubleToPackedString = primShowIntegerToPackedString
// primShowFloatToPackedString  = primShowIntegerToPackedString

// decode a double for a radix b, into (non fractional) Integer and exponent
function decodeFloat(d,b,logb) {
	var sign = 1 ;
	if ( d < 0 ) {
		sign = -1 ;
		d = -d ;
	}
	if ( d == 0 ) {
		return [primIntToInteger(d),0] ;
	}
	var m = Math.floor(d) ;
	var r = d - m ;
	var e = 0 ;
	if ( r > 0 ) {
		// scale up until no fractional part remains
		var d2 = d ;
		do {
			d = d * b ;
			e = e - logb ;
			m = Math.floor(d) ;
			r = d - m ;
		} while ( r > 0 ) ;
		// d = primIntToInteger(sign * d2).shiftLeft(logb).add( primIntToInteger(sign * r * b) ) ;
		d = primIntToInteger(d) ;
	} else {
		// scale down until a fractional part arises
		var d2, e2 ;
		do {
			d2 = d ;
			e2 = e ;
			d = d / b ;
			e = e + logb ;
			m = Math.floor(d) ;
			r = d - m ;
		} while ( r == 0 )
		d = primIntToInteger(d2) ;
		e = e2 ;
	}
	var shift = 53 - d.bitLength() ;
	if ( shift ) {
		d = d.shiftLeft(shift) ;
		e = e - shift ;
	}
	return [sign < 0 ? d.negate() : d, e] ;
}

primDecodeDouble = function(d) {
  var x = decodeFloat(d,2,1);
  return x;
}
primEncodeDouble = function(d,e) {
  return d.doubleValue() * Math.pow(2,e);
}

primIsIEEE = function() {
  return PrimDataBool_True;
}
primRadixDoubleFloat = function() {
  return 2;
}

primIsNaNDouble = function(x) {
  return PrimMkBool(x==Number.NaN);
}
primIsNegativeZeroDouble = function(x) {
  return PrimMkBool(x==-0.0);
}
primIsDenormalizedDouble = function(x) {
  return PrimDataBool_False;
}
primIsInfiniteDouble = function(x) {
  return PrimMkBool(x==Number.POSITIVE_INFINITY || x==Number.NEGATIVE_INFINITY);
}
primDigitsDouble = function() {
  return 53 ;
}
primMaxExpDouble = function() {
  return 1024 ;
}
primMinExpDouble = function() {
  return -1021 ;
}


_MutVar_id_ = 0 ;
_MutVar_.prototype = {
	// identity, a global variable for all MutVar's, used for checking identity equality because this is not offered by javascript
	_id_ : 0
}
function _MutVar_(a) {
	this._val_ = a ;
	this._id_ = ++_MutVar_id_ ;
	// this should be the _id_ of the proto, but I do something wrong:
	// this._id_ = ++this.prototype._id_ ;
}
primNewMutVar 	= function(a,s) {
  return [s,new _MutVar_(a)];
}
primReadMutVar 	= function(m,s) {
  return [s,m._val_];
}
primWriteMutVar = function(m,a,s) {
  m._val_ = a; return s;
}
primSameMutVar 	= function(m1,m2) {
  return PrimMkBool(m1._id_ === m2._id_);
}

primHPutChar = function(h,c) {
 switch(c) {
  case 10 :
   document.writeln("") ;
   break ;
  default :
   document.write(String.fromCharCode(c)) ;
   break ;
 }
 return [] ;
}

// Primitive functions for dealing with JS objects

// primMkCtor :: String -> IO (JSFunPtr c)
primMkCtor = function(nm) {
  if (typeof(window[nm]) !== 'function') {
    primSetCtor(nm, new Function());
  }
  return window[nm];
}

// primMkAnonObj :: IO (JSPtr c)
primMkAnonObj = function() { return {} }

// primMkObj :: JSString -> IO (JSPtr c)
primMkObj     = function(nm) {
  return new (primGetCtor(nm));
}

// Alias to primMkCtor
primGetCtor   = primMkCtor;

// primSetCtor :: JSString -> JSFunPtr c -> IO ()
primSetCtor   = function(nm, fn) {
  window[nm] = fn;
}

// primGetAttr :: JSString -> JSPtr c -> a
primGetAttr   = function(attr, obj) {
  return obj[attr];
}

// primSetAttr :: JSString -> a -> JSPtr c -> IO (JSPtr c)
primSetAttr   = function(attr, val, obj) {
  obj[attr] = val; return obj;
}

// primPureSetAttr :: JSString -> a -> JSPtr c -> JSPtr c
primPureSetAttr = function(attr, val, obj) {
  var clone = primClone(obj);
  primSetAttr(attr, val, clone);
  return clone;
}

// primModAttr :: JSString -> (a -> b) -> JSPtr c -> IO (JSPtr c)
primModAttr   = function (attr, f, obj) {
  primSetAttr(attr, _e_(new _A_(f, [primGetAttr(attr, obj)])), obj);
  return obj;
}

// primPureModAttr :: JSString -> (a -> b) -> JSPtr c -> JSPtr c
primPureModAttr   = function (attr, f, obj) {
  var clone = primClone(obj);
  primModAttr(attr, f, clone);
  return clone;
}


// primGetProtoAttr :: JSString -> JSString -> IO a
primGetProtoAttr = function(attr, cls) {
  primMkCtor(cls);
  return window[cls].prototype[attr];
}

// primSetProtoAttr :: JSString -> a -> JSString -> IO ()
primSetProtoAttr = function(attr, val, cls) {
  primMkCtor(cls);
  window[cls].prototype[attr] = val;
}

// primModProtoAttr :: JSString -> (a -> b) -> JSString -> IO ()
primModProtoAttr = function(attr, f, cls) {
  primSetProtoAttr(attr, _e_(new _A_(f, [primGetProtoAttr(attr, cls)])), cls);
}

// Object cloning facilities

// Clones a JS object
// primClone :: JSPtr a -> JSPtr a
primClone = function(obj) {
  var cloneAlg = function(name, target, copy) {
    target[ name ] = copy;
  };
  return foldObj(cloneAlg, {}, obj, false);
}

// Converts a UHC JS datatype object to a plain JS object
// primToPlainObj :: JSPtr a -> JSPtr b
primToPlainObj = function ( obj ) {
  var toPlainAlg = function(name, target, copy) {
    if (name != "_tag_") {
      target[name] = _e_(copy);
    }
  };
  return foldObj(toPlainAlg, {}, obj, true);
};

foldObj = function (alg, target, original, deep) {
  var name, src, copy, copyIsArray, clone;

  // Extend the base object
  for ( name in original ) {
    src = target[ name ];
    copy = original[ name ];

    // Prevent never-ending loop
    if ( target === copy ) {
      continue;
    }

    // Recurse if we're merging plain objects or arrays
    if (deep && copy && ( isPlainObject(copy) || (copyIsArray = isArray(copy)) ) ) {
      if ( copyIsArray ) {
        copyIsArray = false;
        clone = src && isArray(src) ? src : [];
      } else {
        clone = src && isPlainObject(src) ? src : {};
      }

      // Never move original objects, clone them
      target[ name ] = foldObj(alg, clone, copy, deep);

    // Don't bring in undefined values
    } else if ( copy !== undefined ) {
      alg(name, target, copy);
    }
  }

  // Return the modified object
  return target;
};

type = function( obj ) {
  return obj == null ? String( obj ) : "object";
};

isArray = Array.isArray || function( obj ) {
  return type(obj) === "array";
};

isWindow = function( obj ) {
  return obj && typeof obj === "object" && "setInterval" in obj;
};

isPlainObject = function( obj ) {
  // Must be an Object.
  // Because of IE, we also have to check the presence of the constructor property.
  // Make sure that DOM nodes and window objects don't pass through, as well
  if ( !obj || type(obj) !== "object" || obj.nodeType || isWindow( obj ) ) {
    return false;
  }

  try {
    // Not own constructor property must be Object
    if ( obj.constructor &&
      !hasOwn.call(obj, "constructor") &&
      !hasOwn.call(obj.constructor.prototype, "isPrototypeOf") ) {
      return false;
    }
  } catch ( e ) {
    // IE8,9 Will throw exceptions on certain host objects #9897
    return false;
  }

  // Own properties are enumerated firstly, so to speed up,
  // if last one is own, then all properties are own.

  var key;
  for ( key in obj ) {}

  return key === undefined || hasOwn.call( obj, key );
}

function wrappedThis(cps) {
  return function() {
    var args = Array.prototype.slice.call(arguments);
    args.unshift(this);
    return cps.apply(this, args);
  }
}

primIsFunction = function(a) {
  return PrimMkBool(typeof a === "function");
}

primIsBool = function(a) {
  return PrimMkBool(typeof a === "boolean" || _primIsA(a, Boolean));
}

_primIsNumber = function(a) {
  return typeof a === "number" || _primIsA(a, Number);
}

primIsNumber = function(a) {
  return PrimMkBool(_primIsNumber(a));
}

_primIsString = function(a) {
  return typeof a === "string" || _primIsA(a, String);
}

primIsString = function(a) {
  return PrimMkBool(_primIsString(a));
}

primIsChar = function(a) {
  return PrimMkBool(_primIsString(a) && a.length == 1);
}

primIsInt = function(a) {
  return PrimMkBool(_primIsNumber(a) && parseFloat(a) == parseInt(a, 10) && !isNaN(a));
}

primIsDouble = function(a) {
  return PrimMkBool(_primIsNumber(a) && parseFloat(a) != parseInt(a, 10) && !isNaN(a));
}

primIsNull = function(a) {
  //typeof does not work, known bug.
  return PrimMkBool(a === null);
}

primIsUndefined = function(a) {
  return PrimMkBool(typeof a === "undefined");
}

primIsObject = function(a) {
  return PrimMkBool(typeof a === "object" && a !== null);
}

_primIsA = function(a, b) {
  //if a isObject and b isFunction
  if(typeof a === "object" && a !== null && typeof b === "function") {
    return a.constructor == b;
  }
  return false;
}

primIsA = function(a, b) {
  return PrimMkBool(_primIsA(a,b));
}

primInstanceOf = function(a, b) {
  if(typeof a === "object" && typeof b === "function") {
    return PrimMkBool(a instanceof b);
  }
  return PrimMkBool(false);
}

primEq = function(a, b) {
  return PrimMkBool(a == b);
}

primCharToUpper = function(c) {
  return String.fromCharCode(c).toUpperCase().charCodeAt(0);
}
// JCU
var $Language=
 ($Language ? $Language : {});
var $Language=
 ($Language ? $Language : {});
$Language.$UHC=
 ($Language.$UHC ? $Language.$UHC : {});
var $ParseLib=
 ($ParseLib ? $ParseLib : {});
$Language.$UHC=
 ($Language.$UHC ? $Language.$UHC : {});
$Language.$Prolog=
 ($Language.$Prolog ? $Language.$Prolog : {});
$Language.$UHC.$JS=
 ($Language.$UHC.$JS ? $Language.$UHC.$JS : {});
$ParseLib.$Abstract=
 ($ParseLib.$Abstract ? $ParseLib.$Abstract : {});
$Language.$UHC.$JS=
 ($Language.$UHC.$JS ? $Language.$UHC.$JS : {});
$Language.$Prolog.$NanoProlog=
 ($Language.$Prolog.$NanoProlog ? $Language.$Prolog.$NanoProlog : {});
$Language.$UHC.$JS.$JQuery=
 ($Language.$UHC.$JS.$JQuery ? $Language.$UHC.$JS.$JQuery : {});
var $Data=
 ($Data ? $Data : {});
$Language.$UHC.$JS.$W3C=
 ($Language.$UHC.$JS.$W3C ? $Language.$UHC.$JS.$W3C : {});
var $UHC=
 ($UHC ? $UHC : {});
var $Control=
 ($Control ? $Control : {});
$ParseLib.$Simple=
 ($ParseLib.$Simple ? $ParseLib.$Simple : {});
$Language.$UHC.$JS.$ECMA=
 ($Language.$UHC.$JS.$ECMA ? $Language.$UHC.$JS.$ECMA : {});
$ParseLib.$Abstract.$Core=
 ($ParseLib.$Abstract.$Core ? $ParseLib.$Abstract.$Core : {});
$Language.$UHC.$JS.$Prelude=
 ($Language.$UHC.$JS.$Prelude ? $Language.$UHC.$JS.$Prelude : {});
$Language.$Prolog.$NanoProlog.$ParserUUTC=
 ($Language.$Prolog.$NanoProlog.$ParserUUTC ? $Language.$Prolog.$NanoProlog.$ParserUUTC : {});
$Language.$UHC.$JS.$JQuery.$Draggable=
 ($Language.$UHC.$JS.$JQuery.$Draggable ? $Language.$UHC.$JS.$JQuery.$Draggable : {});
$Data.$Map=
 ($Data.$Map ? $Data.$Map : {});
var $JCU=
 ($JCU ? $JCU : {});
var $Util=
 ($Util ? $Util : {});
$Language.$UHC.$JS.$Primitives=
 ($Language.$UHC.$JS.$Primitives ? $Language.$UHC.$JS.$Primitives : {});
$Language.$UHC.$JS.$W3C.$HTML5=
 ($Language.$UHC.$JS.$W3C.$HTML5 ? $Language.$UHC.$JS.$W3C.$HTML5 : {});
var $Prolog=
 ($Prolog ? $Prolog : {});
$Language.$UHC.$JS.$JQuery.$JQuery=
 ($Language.$UHC.$JS.$JQuery.$JQuery ? $Language.$UHC.$JS.$JQuery.$JQuery : {});
var $Templates=
 ($Templates ? $Templates : {});
$UHC.$OldIO=
 ($UHC.$OldIO ? $UHC.$OldIO : {});
$Language.$UHC.$JS.$Types=
 ($Language.$UHC.$JS.$Types ? $Language.$UHC.$JS.$Types : {});
$Data.$List=
 ($Data.$List ? $Data.$List : {});
$Control.$Applicative=
 ($Control.$Applicative ? $Control.$Applicative : {});
$ParseLib.$Simple.$Core=
 ($ParseLib.$Simple.$Core ? $ParseLib.$Simple.$Core : {});
$Data.$LocalStorage=
 ($Data.$LocalStorage ? $Data.$LocalStorage : {});
$Data.$Maybe=
 ($Data.$Maybe ? $Data.$Maybe : {});
$Control.$Monad=
 ($Control.$Monad ? $Control.$Monad : {});
$UHC.$Base=
 ($UHC.$Base ? $UHC.$Base : {});
$ParseLib.$Abstract.$Derived=
 ($ParseLib.$Abstract.$Derived ? $ParseLib.$Abstract.$Derived : {});
$Language.$Prolog.$NanoProlog.$NanoProlog=
 ($Language.$Prolog.$NanoProlog.$NanoProlog ? $Language.$Prolog.$NanoProlog.$NanoProlog : {});
$Language.$UHC.$JS.$Assorted=
 ($Language.$UHC.$JS.$Assorted ? $Language.$UHC.$JS.$Assorted : {});
$UHC.$IOBase=
 ($UHC.$IOBase ? $UHC.$IOBase : {});
$Language.$UHC.$JS.$ECMA.$String=
 ($Language.$UHC.$JS.$ECMA.$String ? $Language.$UHC.$JS.$ECMA.$String : {});
$Data.$Tree=
 ($Data.$Tree ? $Data.$Tree : {});
var $Debug=
 ($Debug ? $Debug : {});
var $Models=
 ($Models ? $Models : {});
$Language.$UHC.$JS.$ECMA.$Bool=
 ($Language.$UHC.$JS.$ECMA.$Bool ? $Language.$UHC.$JS.$ECMA.$Bool : {});
$ParseLib.$Abstract.$Applications=
 ($ParseLib.$Abstract.$Applications ? $ParseLib.$Abstract.$Applications : {});
$UHC.$Run=
 ($UHC.$Run ? $UHC.$Run : {});
$Language.$UHC.$JS.$JQuery.$Droppable=
 ($Language.$UHC.$JS.$JQuery.$Droppable ? $Language.$UHC.$JS.$JQuery.$Droppable : {});
$UHC.$Base.$__74__328__0DFLUHC_2eBase_2eshowsPrec=
 new _F_(function($d,$x__1)
         {var $x__13=
           _e_($x__1);
          var $__swJSW0__0;
          switch($x__13._tag_)
           {case 0:
             var $__=
              new _A_($UHC.$Base.$showsPrec,[$UHC.$Base.$Show__DCT74__128__0,11,$x__13._1]);
             var $__6=
              new _A_($UHC.$Base.$packedStringToString,["ExitFailure "]);
             var $__7=
              new _A_($UHC.$Base.$showString,[$__6]);
             var $__8=
              new _A_($UHC.$Base.$_2e,[$__7,$__]);
             var $__9=
              new _A_($UHC.$Base.$primGtInt,[$d,10]);
             var $__10=
              new _A_($UHC.$Base.$showParen,[$__9,$__8]);
             $__swJSW0__0=
              $__10;
             break;
            case 1:
             var $__=
              new _A_($UHC.$Base.$packedStringToString,["ExitSuccess"]);
             var $__12=
              new _A_($UHC.$Base.$showString,[$__]);
             $__swJSW0__0=
              $__12;
             break;}
          return $__swJSW0__0;});
$UHC.$Base.$__74__328__0NEW6538UNQ9522EVLRDC=
 new _F_(function($__)
         {var $Show__=
           _e_(new _A_($UHC.$Base.$Show__CLS74__43__0,[$__]));
          var $__6=
           {_tag_:0,_1:$Show__._1,_2:$Show__._2,_3:$UHC.$Base.$__74__328__0DFLUHC_2eBase_2eshowsPrec};
          return $__6;});
$UHC.$Base.$__74__328__0NEW6536UNQ9520RDC=
 new _F_(function($__)
         {var $__2=
           new _A_($UHC.$Base.$__74__328__0NEW6538UNQ9522EVLRDC,[$__]);
          return $__2;});
$UHC.$Base.$__74__328__0UNQ9520RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$__74__328__0NEW6536UNQ9520RDC,[$UHC.$Base.$__74__328__0UNQ9520RDC]);}),[]);
$UHC.$Base.$__74__328__0=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$__74__328__0UNQ9520RDC;}),[]);
$UHC.$IOBase.$Show__DCT230__22__0DFLUHC_2eBase_2eshowsPrec=
 new _F_(function($x1,$x2)
         {var $x23=
           _e_($x2);
          var $__swJSW2__0;
          switch($x23._tag_)
           {case 0:
             var $__=
              new _A_($UHC.$Base.$packedStringToString,["denormal"]);
             var $__5=
              new _A_($UHC.$Base.$showString,[$__]);
             $__swJSW2__0=
              $__5;
             break;
            case 1:
             var $__=
              new _A_($UHC.$Base.$packedStringToString,["divide by zero"]);
             var $__7=
              new _A_($UHC.$Base.$showString,[$__]);
             $__swJSW2__0=
              $__7;
             break;
            case 2:
             var $__=
              new _A_($UHC.$Base.$packedStringToString,["loss of precision"]);
             var $__9=
              new _A_($UHC.$Base.$showString,[$__]);
             $__swJSW2__0=
              $__9;
             break;
            case 3:
             var $__=
              new _A_($UHC.$Base.$packedStringToString,["arithmetic overflow"]);
             var $__11=
              new _A_($UHC.$Base.$showString,[$__]);
             $__swJSW2__0=
              $__11;
             break;
            case 4:
             var $__=
              new _A_($UHC.$Base.$packedStringToString,["arithmetic underflow"]);
             var $__13=
              new _A_($UHC.$Base.$showString,[$__]);
             $__swJSW2__0=
              $__13;
             break;}
          return $__swJSW2__0;});
$UHC.$IOBase.$Show__NEW217UNQ1681EVLDCT230__22__0RDC=
 new _F_(function($Show__)
         {var $Show__2=
           _e_(new _A_($UHC.$Base.$Show__CLS74__43__0,[$Show__]));
          var $__6=
           {_tag_:0,_1:$Show__2._1,_2:$Show__2._2,_3:$UHC.$IOBase.$Show__DCT230__22__0DFLUHC_2eBase_2eshowsPrec};
          return $__6;});
$UHC.$IOBase.$Show__NEW215UNQ1680DCT230__22__0RDC=
 new _F_(function($Show__)
         {var $Show__2=
           new _A_($UHC.$IOBase.$Show__NEW217UNQ1681EVLDCT230__22__0RDC,[$Show__]);
          return $Show__2;});
$UHC.$IOBase.$Show__UNQ1680DCT230__22__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$IOBase.$Show__NEW215UNQ1680DCT230__22__0RDC,[$UHC.$IOBase.$Show__UNQ1680DCT230__22__0RDC]);}),[]);
$UHC.$IOBase.$Show__DCT230__22__0=
 new _A_(new _F_(function()
                 {return $UHC.$IOBase.$Show__UNQ1680DCT230__22__0RDC;}),[]);
$UHC.$IOBase.$Show__DCT230__24__0DFLUHC_2eBase_2eshowsPrec=
 new _F_(function($x1,$x2)
         {var $x23=
           _e_($x2);
          var $__swJSW4__0;
          switch($x23._tag_)
           {case 0:
             var $__=
              new _A_($UHC.$Base.$packedStringToString,["heap overflow"]);
             var $__5=
              new _A_($UHC.$Base.$showString,[$__]);
             $__swJSW4__0=
              $__5;
             break;
            case 1:
             var $__=
              new _A_($UHC.$Base.$showString,[$x23._1]);
             var $__8=
              new _A_($UHC.$Base.$packedStringToString,["stack overflow: "]);
             var $__9=
              new _A_($UHC.$Base.$showString,[$__8]);
             var $__10=
              new _A_($UHC.$Base.$_2e,[$__9,$__]);
             $__swJSW4__0=
              $__10;
             break;
            case 2:
             var $__=
              new _A_($UHC.$Base.$packedStringToString,["thread killed"]);
             var $__12=
              new _A_($UHC.$Base.$showString,[$__]);
             $__swJSW4__0=
              $__12;
             break;}
          return $__swJSW4__0;});
$UHC.$IOBase.$Show__NEW234UNQ1708EVLDCT230__24__0RDC=
 new _F_(function($Show__)
         {var $Show__2=
           _e_(new _A_($UHC.$Base.$Show__CLS74__43__0,[$Show__]));
          var $__6=
           {_tag_:0,_1:$Show__2._1,_2:$Show__2._2,_3:$UHC.$IOBase.$Show__DCT230__24__0DFLUHC_2eBase_2eshowsPrec};
          return $__6;});
$UHC.$IOBase.$Show__NEW232UNQ1707DCT230__24__0RDC=
 new _F_(function($Show__)
         {var $Show__2=
           new _A_($UHC.$IOBase.$Show__NEW234UNQ1708EVLDCT230__24__0RDC,[$Show__]);
          return $Show__2;});
$UHC.$IOBase.$Show__UNQ1707DCT230__24__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$IOBase.$Show__NEW232UNQ1707DCT230__24__0RDC,[$UHC.$IOBase.$Show__UNQ1707DCT230__24__0RDC]);}),[]);
$UHC.$IOBase.$Show__DCT230__24__0=
 new _A_(new _F_(function()
                 {return $UHC.$IOBase.$Show__UNQ1707DCT230__24__0RDC;}),[]);
$UHC.$IOBase.$Show__DCT230__19__0DFLUHC_2eBase_2eshow=
 new _F_(function($x)
         {var $__=
           _e_($x);
          var $__swJSW6__0;
          switch($__._tag_)
           {case 0:
             var $__3=
              new _A_($UHC.$Base.$packedStringToString,["already exists"]);
             $__swJSW6__0=
              $__3;
             break;
            case 1:
             var $__4=
              new _A_($UHC.$Base.$packedStringToString,["resource already in use"]);
             $__swJSW6__0=
              $__4;
             break;
            case 2:
             var $__5=
              new _A_($UHC.$Base.$packedStringToString,["does not exist"]);
             $__swJSW6__0=
              $__5;
             break;
            case 3:
             var $__6=
              new _A_($UHC.$Base.$packedStringToString,["end of file"]);
             $__swJSW6__0=
              $__6;
             break;
            case 4:
             $__swJSW6__0=
              $UHC.$Base.$undefined;
             break;
            case 5:
             var $__7=
              new _A_($UHC.$Base.$packedStringToString,["illegal operation"]);
             $__swJSW6__0=
              $__7;
             break;
            case 6:
             var $__8=
              new _A_($UHC.$Base.$packedStringToString,["inappropriate type"]);
             $__swJSW6__0=
              $__8;
             break;
            case 7:
             var $__9=
              new _A_($UHC.$Base.$packedStringToString,["interrupted"]);
             $__swJSW6__0=
              $__9;
             break;
            case 8:
             var $__10=
              new _A_($UHC.$Base.$packedStringToString,["invalid argument"]);
             $__swJSW6__0=
              $__10;
             break;
            case 9:
             var $__11=
              new _A_($UHC.$Base.$packedStringToString,["does not exist"]);
             $__swJSW6__0=
              $__11;
             break;
            case 10:
             var $__12=
              new _A_($UHC.$Base.$packedStringToString,["other error"]);
             $__swJSW6__0=
              $__12;
             break;
            case 11:
             var $__13=
              new _A_($UHC.$Base.$packedStringToString,["permission denied"]);
             $__swJSW6__0=
              $__13;
             break;
            case 12:
             var $__14=
              new _A_($UHC.$Base.$packedStringToString,["resource already in use"]);
             $__swJSW6__0=
              $__14;
             break;
            case 13:
             var $__15=
              new _A_($UHC.$Base.$packedStringToString,["resource exhausted"]);
             $__swJSW6__0=
              $__15;
             break;
            case 14:
             var $__16=
              new _A_($UHC.$Base.$packedStringToString,["unsuppored operation"]);
             $__swJSW6__0=
              $__16;
             break;
            case 15:
             var $__17=
              new _A_($UHC.$Base.$packedStringToString,["user error"]);
             $__swJSW6__0=
              $__17;
             break;}
          return $__swJSW6__0;});
$UHC.$IOBase.$Show__NEW198UNQ1807EVLDCT230__19__0RDC=
 new _F_(function($Show__)
         {var $Show__2=
           _e_(new _A_($UHC.$Base.$Show__CLS74__43__0,[$Show__]));
          var $__6=
           {_tag_:0,_1:$UHC.$IOBase.$Show__DCT230__19__0DFLUHC_2eBase_2eshow,_2:$Show__2._2,_3:$Show__2._3};
          return $__6;});
$UHC.$IOBase.$Show__NEW196UNQ1806DCT230__19__0RDC=
 new _F_(function($Show__)
         {var $Show__2=
           new _A_($UHC.$IOBase.$Show__NEW198UNQ1807EVLDCT230__19__0RDC,[$Show__]);
          return $Show__2;});
$UHC.$IOBase.$Show__UNQ1806DCT230__19__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$IOBase.$Show__NEW196UNQ1806DCT230__19__0RDC,[$UHC.$IOBase.$Show__UNQ1806DCT230__19__0RDC]);}),[]);
$UHC.$IOBase.$Show__DCT230__19__0=
 new _A_(new _F_(function()
                 {return $UHC.$IOBase.$Show__UNQ1806DCT230__19__0RDC;}),[]);
$UHC.$IOBase.$__234__608NEW283=
 new _F_(function($s)
         {var $__=
           new _A_($UHC.$Base.$packedStringToString,[")"]);
          var $__3=
           new _A_($UHC.$Base.$showString,[$__]);
          var $__4=
           new _A_($UHC.$Base.$showString,[$s]);
          var $__5=
           new _A_($UHC.$Base.$_2e,[$__4,$__3]);
          var $__6=
           new _A_($UHC.$Base.$packedStringToString,[" ("]);
          var $__7=
           new _A_($UHC.$Base.$showString,[$__6]);
          var $__8=
           new _A_($UHC.$Base.$_2e,[$__7,$__5]);
          var $__9=
           _e_($s);
          var $__swJSW8__0;
          switch($__9._tag_)
           {case 0:
             $__swJSW8__0=
              $__8;
             break;
            case 1:
             $__swJSW8__0=
              $UHC.$Base.$id;
             break;}
          return $__swJSW8__0;});
$UHC.$IOBase.$showHandle=
 new _F_(function($file)
         {var $__=
           new _A_($UHC.$Base.$packedStringToString,["}"]);
          var $__3=
           new _A_($UHC.$Base.$showString,[$__]);
          var $__4=
           new _A_($UHC.$Base.$showString,[$file]);
          var $__5=
           new _A_($UHC.$Base.$_2e,[$__4,$__3]);
          var $__6=
           new _A_($UHC.$Base.$packedStringToString,["{handle: "]);
          var $__7=
           new _A_($UHC.$Base.$showString,[$__6]);
          return new _A_($UHC.$Base.$_2e,[$__7,$__5]);});
$UHC.$IOBase.$Show__DCT230__13__0DFLUHC_2eBase_2eshowsPrec=
 new _F_(function($__,$h)
         {var $__3=
           new _A_($UHC.$Base.$packedStringToString,["<handle>"]);
          return new _A_($UHC.$Base.$showString,[$__3]);});
$UHC.$IOBase.$Show__NEW264UNQ2286EVLDCT230__13__0RDC=
 new _F_(function($Show__)
         {var $Show__2=
           _e_(new _A_($UHC.$Base.$Show__CLS74__43__0,[$Show__]));
          var $__6=
           {_tag_:0,_1:$Show__2._1,_2:$Show__2._2,_3:$UHC.$IOBase.$Show__DCT230__13__0DFLUHC_2eBase_2eshowsPrec};
          return $__6;});
$UHC.$IOBase.$Show__NEW262UNQ2285DCT230__13__0RDC=
 new _F_(function($Show__)
         {var $Show__2=
           new _A_($UHC.$IOBase.$Show__NEW264UNQ2286EVLDCT230__13__0RDC,[$Show__]);
          return $Show__2;});
$UHC.$IOBase.$Show__UNQ2285DCT230__13__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$IOBase.$Show__NEW262UNQ2285DCT230__13__0RDC,[$UHC.$IOBase.$Show__UNQ2285DCT230__13__0RDC]);}),[]);
$UHC.$IOBase.$Show__DCT230__13__0=
 new _A_(new _F_(function()
                 {return $UHC.$IOBase.$Show__UNQ2285DCT230__13__0RDC;}),[]);
$UHC.$IOBase.$Show__DCT230__16__0DFLUHC_2eBase_2eshowsPrec=
 new _F_(function($x1,$x2)
         {var $x23=
           _e_($x2);
          var $__swJSW10__0;
          switch($x23._tag_)
           {case 0:
             var $__7=
              new _A_($UHC.$IOBase.$showHandle,[$x23._1]);
             $__swJSW10__0=
              $__7;
             break;
            case 1:
             var $__10=
              new _A_($UHC.$IOBase.$showHandle,[$x23._1]);
             $__swJSW10__0=
              $__10;
             break;
            case 2:
             var $__=
              new _A_($UHC.$Base.$shows,[$UHC.$IOBase.$Show__DCT230__13__0,$x23._1]);
             $__swJSW10__0=
              $__;
             break;}
          return $__swJSW10__0;});
$UHC.$IOBase.$Show__NEW276UNQ2511EVLDCT230__16__0RDC=
 new _F_(function($Show__)
         {var $Show__2=
           _e_(new _A_($UHC.$Base.$Show__CLS74__43__0,[$Show__]));
          var $__6=
           {_tag_:0,_1:$Show__2._1,_2:$Show__2._2,_3:$UHC.$IOBase.$Show__DCT230__16__0DFLUHC_2eBase_2eshowsPrec};
          return $__6;});
$UHC.$IOBase.$Show__NEW274UNQ2509DCT230__16__0RDC=
 new _F_(function($Show__)
         {var $Show__2=
           new _A_($UHC.$IOBase.$Show__NEW276UNQ2511EVLDCT230__16__0RDC,[$Show__]);
          return $Show__2;});
$UHC.$IOBase.$Show__UNQ2509DCT230__16__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$IOBase.$Show__NEW274UNQ2509DCT230__16__0RDC,[$UHC.$IOBase.$Show__UNQ2509DCT230__16__0RDC]);}),[]);
$UHC.$IOBase.$Show__DCT230__16__0=
 new _A_(new _F_(function()
                 {return $UHC.$IOBase.$Show__UNQ2509DCT230__16__0RDC;}),[]);
$UHC.$IOBase.$__234__577NEW303=
 new _F_(function($p,$hdl,$fn)
         {var $__=
           _e_($fn);
          var $__swJSW12__0;
          switch($__._tag_)
           {case 0:
             var $__6=
              new _A_($UHC.$Base.$packedStringToString,[": "]);
             var $__7=
              new _A_($UHC.$Base.$showString,[$__6]);
             var $__8=
              new _A_($UHC.$Base.$showString,[$__._1]);
             var $__9=
              new _A_($UHC.$Base.$_2e,[$__8,$__7]);
             $__swJSW12__0=
              $__9;
             break;
            case 1:
             var $__10=
              _e_($hdl);
             var $__swJSW13__0;
             switch($__10._tag_)
              {case 0:
                var $__12=
                 new _A_($UHC.$Base.$packedStringToString,[": "]);
                var $__13=
                 new _A_($UHC.$Base.$showString,[$__12]);
                var $__14=
                 new _A_($UHC.$Base.$showsPrec,[$UHC.$IOBase.$Show__DCT230__16__0,$p,$__10._1]);
                var $__15=
                 new _A_($UHC.$Base.$_2e,[$__14,$__13]);
                $__swJSW13__0=
                 $__15;
                break;
               case 1:
                $__swJSW13__0=
                 $UHC.$Base.$id;
                break;}
             $__swJSW12__0=
              $__swJSW13__0;
             break;}
          return $__swJSW12__0;});
$UHC.$IOBase.$__234__595NEW295=
 new _F_(function($loc)
         {var $__=
           new _A_($UHC.$Base.$packedStringToString,[": "]);
          var $__3=
           new _A_($UHC.$Base.$showString,[$__]);
          var $__4=
           new _A_($UHC.$Base.$showString,[$loc]);
          var $__5=
           new _A_($UHC.$Base.$_2e,[$__4,$__3]);
          var $__6=
           _e_($loc);
          var $__swJSW14__0;
          switch($__6._tag_)
           {case 0:
             $__swJSW14__0=
              $__5;
             break;
            case 1:
             $__swJSW14__0=
              $UHC.$Base.$id;
             break;}
          return $__swJSW14__0;});
$UHC.$IOBase.$Show__DCT230__20__0DFLUHC_2eBase_2eshowsPrec=
 new _F_(function($p,$__)
         {var $__3=
           _e_($__);
          var $__9=
           new _A_($UHC.$IOBase.$__234__608NEW283,[$__3.ioe__description]);
          var $__10=
           new _A_($UHC.$Base.$showsPrec,[$UHC.$IOBase.$Show__DCT230__19__0,$p,$__3.ioe__type]);
          var $__11=
           new _A_($UHC.$Base.$_2e,[$__10,$__9]);
          var $__12=
           new _A_($UHC.$IOBase.$__234__595NEW295,[$__3.ioe__location]);
          var $__13=
           new _A_($UHC.$Base.$_2e,[$__12,$__11]);
          var $__14=
           new _A_($UHC.$IOBase.$__234__577NEW303,[$p,$__3.ioe__handle,$__3.ioe__filename]);
          var $__15=
           new _A_($UHC.$Base.$_2e,[$__14,$__13]);
          return $__15;});
$UHC.$IOBase.$Show__NEW320UNQ2414EVLDCT230__20__0RDC=
 new _F_(function($Show__)
         {var $Show__2=
           _e_(new _A_($UHC.$Base.$Show__CLS74__43__0,[$Show__]));
          var $__6=
           {_tag_:0,_1:$Show__2._1,_2:$Show__2._2,_3:$UHC.$IOBase.$Show__DCT230__20__0DFLUHC_2eBase_2eshowsPrec};
          return $__6;});
$UHC.$IOBase.$Show__NEW318UNQ2411DCT230__20__0RDC=
 new _F_(function($Show__)
         {var $Show__2=
           new _A_($UHC.$IOBase.$Show__NEW320UNQ2414EVLDCT230__20__0RDC,[$Show__]);
          return $Show__2;});
$UHC.$IOBase.$Show__UNQ2411DCT230__20__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$IOBase.$Show__NEW318UNQ2411DCT230__20__0RDC,[$UHC.$IOBase.$Show__UNQ2411DCT230__20__0RDC]);}),[]);
$UHC.$IOBase.$Show__DCT230__20__0=
 new _A_(new _F_(function()
                 {return $UHC.$IOBase.$Show__UNQ2411DCT230__20__0RDC;}),[]);
$UHC.$IOBase.$Show__DCT230__23__0DFLUHC_2eBase_2eshowsPrec=
 new _F_(function($x1,$x2)
         {var $x23=
           _e_($x2);
          var $__swJSW17__0;
          switch($x23._tag_)
           {case 0:
             var $__=
              new _A_($UHC.$Base.$packedStringToString,["array index out of range"]);
             var $__6=
              new _A_($UHC.$IOBase.$showException,[$__,$x23._1]);
             $__swJSW17__0=
              $__6;
             break;
            case 1:
             var $__=
              new _A_($UHC.$Base.$packedStringToString,["undefined array element"]);
             var $__9=
              new _A_($UHC.$IOBase.$showException,[$__,$x23._1]);
             $__swJSW17__0=
              $__9;
             break;}
          return $__swJSW17__0;});
$UHC.$IOBase.$Show__NEW1234UNQ1731EVLDCT230__23__0RDC=
 new _F_(function($Show__)
         {var $Show__2=
           _e_(new _A_($UHC.$Base.$Show__CLS74__43__0,[$Show__]));
          var $__6=
           {_tag_:0,_1:$Show__2._1,_2:$Show__2._2,_3:$UHC.$IOBase.$Show__DCT230__23__0DFLUHC_2eBase_2eshowsPrec};
          return $__6;});
$UHC.$IOBase.$Show__NEW1232UNQ1730DCT230__23__0RDC=
 new _F_(function($Show__)
         {var $Show__2=
           new _A_($UHC.$IOBase.$Show__NEW1234UNQ1731EVLDCT230__23__0RDC,[$Show__]);
          return $Show__2;});
$UHC.$IOBase.$Show__UNQ1730DCT230__23__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$IOBase.$Show__NEW1232UNQ1730DCT230__23__0RDC,[$UHC.$IOBase.$Show__UNQ1730DCT230__23__0RDC]);}),[]);
$UHC.$IOBase.$Show__DCT230__23__0=
 new _A_(new _F_(function()
                 {return $UHC.$IOBase.$Show__UNQ1730DCT230__23__0RDC;}),[]);
$UHC.$IOBase.$__234__2216NEW1216=
 new _F_(function($msg)
         {var $__=
           new _A_($UHC.$Base.$null,[$msg]);
          var $__3=
           _e_($__);
          var $__swJSW19__0;
          switch($__3._tag_)
           {case 0:
             var $__4=
              new _A_($UHC.$Base.$showString,[$msg]);
             var $__5=
              new _A_($UHC.$Base.$packedStringToString,[": "]);
             var $__6=
              new _A_($UHC.$Base.$showString,[$__5]);
             var $__7=
              new _A_($UHC.$Base.$_2e,[$__6,$__4]);
             $__swJSW19__0=
              $__7;
             break;
            case 1:
             $__swJSW19__0=
              $UHC.$Base.$id;
             break;}
          return $__swJSW19__0;});
$UHC.$IOBase.$showException=
 new _F_(function($tag,$msg)
         {var $__=
           new _A_($UHC.$IOBase.$__234__2216NEW1216,[$msg]);
          var $__4=
           new _A_($UHC.$Base.$showString,[$tag]);
          return new _A_($UHC.$Base.$_2e,[$__4,$__]);});
$UHC.$IOBase.$Show__DCT230__21__0DFLUHC_2eBase_2eshowsPrec=
 new _F_(function($x1,$x2)
         {var $x23=
           _e_($x2);
          var $__swJSW20__0;
          switch($x23._tag_)
           {case 0:
             var $__=
              new _A_($UHC.$Base.$shows,[$UHC.$IOBase.$Show__DCT230__22__0,$x23._1]);
             $__swJSW20__0=
              $__;
             break;
            case 1:
             var $__=
              new _A_($UHC.$Base.$shows,[$UHC.$IOBase.$Show__DCT230__23__0,$x23._1]);
             $__swJSW20__0=
              $__;
             break;
            case 2:
             var $__=
              new _A_($UHC.$Base.$packedStringToString,["assertion failed"]);
             var $__10=
              new _A_($UHC.$IOBase.$showException,[$__,$x23._1]);
             $__swJSW20__0=
              $__10;
             break;
            case 3:
             var $__=
              new _A_($UHC.$Base.$shows,[$UHC.$IOBase.$Show__DCT230__24__0,$x23._1]);
             $__swJSW20__0=
              $__;
             break;
            case 4:
             var $__=
              new _A_($UHC.$Base.$packedStringToString,["thread blocked indefinitely"]);
             var $__14=
              new _A_($UHC.$Base.$showString,[$__]);
             $__swJSW20__0=
              $__14;
             break;
            case 5:
             var $__=
              new _A_($UHC.$Base.$packedStringToString,["<<deadlock>>"]);
             var $__16=
              new _A_($UHC.$Base.$showString,[$__]);
             $__swJSW20__0=
              $__16;
             break;
            case 6:
             var $__=
              new _A_($UHC.$Base.$showString,[$x23._1]);
             $__swJSW20__0=
              $__;
             break;
            case 7:
             var $__=
              new _A_($UHC.$Base.$shows,[$UHC.$Base.$__74__328__0,$x23._1]);
             var $__21=
              new _A_($UHC.$Base.$packedStringToString,["exit: "]);
             var $__22=
              new _A_($UHC.$Base.$showString,[$__21]);
             var $__23=
              new _A_($UHC.$Base.$_2e,[$__22,$__]);
             $__swJSW20__0=
              $__23;
             break;
            case 8:
             var $__=
              new _A_($UHC.$Base.$shows,[$UHC.$IOBase.$Show__DCT230__20__0,$x23._1]);
             $__swJSW20__0=
              $__;
             break;
            case 9:
             var $__=
              new _A_($UHC.$Base.$packedStringToString,["undefined member"]);
             var $__28=
              new _A_($UHC.$IOBase.$showException,[$__,$x23._1]);
             $__swJSW20__0=
              $__28;
             break;
            case 10:
             var $__=
              new _A_($UHC.$Base.$packedStringToString,["<<loop>>"]);
             var $__30=
              new _A_($UHC.$Base.$showString,[$__]);
             $__swJSW20__0=
              $__30;
             break;
            case 11:
             var $__=
              new _A_($UHC.$Base.$packedStringToString,["pattern match failure"]);
             var $__33=
              new _A_($UHC.$IOBase.$showException,[$__,$x23._1]);
             $__swJSW20__0=
              $__33;
             break;
            case 12:
             var $__=
              new _A_($UHC.$Base.$packedStringToString,["undefined field"]);
             var $__36=
              new _A_($UHC.$IOBase.$showException,[$__,$x23._1]);
             $__swJSW20__0=
              $__36;
             break;
            case 13:
             var $__=
              new _A_($UHC.$Base.$packedStringToString,["select of missing field"]);
             var $__39=
              new _A_($UHC.$IOBase.$showException,[$__,$x23._1]);
             $__swJSW20__0=
              $__39;
             break;
            case 14:
             var $__=
              new _A_($UHC.$Base.$packedStringToString,["update of missing field"]);
             var $__42=
              new _A_($UHC.$IOBase.$showException,[$__,$x23._1]);
             $__swJSW20__0=
              $__42;
             break;}
          return $__swJSW20__0;});
$UHC.$IOBase.$Show__NEW1270UNQ2331EVLDCT230__21__0RDC=
 new _F_(function($Show__)
         {var $Show__2=
           _e_(new _A_($UHC.$Base.$Show__CLS74__43__0,[$Show__]));
          var $__6=
           {_tag_:0,_1:$Show__2._1,_2:$Show__2._2,_3:$UHC.$IOBase.$Show__DCT230__21__0DFLUHC_2eBase_2eshowsPrec};
          return $__6;});
$UHC.$IOBase.$Show__NEW1268UNQ2325DCT230__21__0RDC=
 new _F_(function($Show__)
         {var $Show__2=
           new _A_($UHC.$IOBase.$Show__NEW1270UNQ2331EVLDCT230__21__0RDC,[$Show__]);
          return $Show__2;});
$UHC.$IOBase.$Show__UNQ2325DCT230__21__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$IOBase.$Show__NEW1268UNQ2325DCT230__21__0RDC,[$UHC.$IOBase.$Show__UNQ2325DCT230__21__0RDC]);}),[]);
$UHC.$IOBase.$Show__DCT230__21__0=
 new _A_(new _F_(function()
                 {return $UHC.$IOBase.$Show__UNQ2325DCT230__21__0RDC;}),[]);
$UHC.$OldIO.$__240__72=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["stdout"]);}),[]);
$UHC.$IOBase.$JSHandle__=
 new _F_(function($x1)
         {return {_tag_:0,_1:$x1};});
$UHC.$OldIO.$__240__71=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$IOBase.$JSHandle__,[$UHC.$OldIO.$__240__72]);}),[]);
$UHC.$IOBase.$OldHandle__=
 new _F_(function($x1)
         {return {_tag_:2,_1:$x1};});
$UHC.$OldIO.$stdout=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$IOBase.$OldHandle__,[$UHC.$OldIO.$__240__71]);}),[]);
$UHC.$Base.$head=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          var $__swJSW22__0;
          switch($__2._tag_)
           {case 0:
             $__swJSW22__0=
              $__2._1;
             break;
            case 1:
             $__swJSW22__0=
              $UHC.$Base.$undefined;
             break;}
          return $__swJSW22__0;});
$UHC.$OldIO.$hPutStr=
 new _F_(function($h,$s)
         {var $__=
           new _A_($UHC.$Base.$null,[$s]);
          var $__4=
           _e_($__);
          var $__swJSW23__0;
          switch($__4._tag_)
           {case 0:
             var $__5=
              new _A_($UHC.$Base.$tail,[$s]);
             var $__6=
              new _A_($UHC.$OldIO.$hPutStr,[$h,$__5]);
             var $__7=
              new _A_($UHC.$Base.$head,[$s]);
             var $__8=
              new _A_($UHC.$OldIO.$hPutChar,[$h,$__7]);
             var $__9=
              new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__8,$__6]);
             $__swJSW23__0=
              $__9;
             break;
            case 1:
             var $__10=
              new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0,[]]);
             $__swJSW23__0=
              $__10;
             break;}
          return $__swJSW23__0;});
$UHC.$OldIO.$primHPutChar=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__2);
          return primHPutChar($__3,$__4);});
$UHC.$OldIO.$__240__93__0=
 new _F_(function($h,$c,$__)
         {return new _A_($UHC.$OldIO.$primHPutChar,[$h,$c]);});
$UHC.$OldIO.$hPutChar=
 new _F_(function($h,$c)
         {var $__=
           new _A_($UHC.$OldIO.$__240__93__0,[$h,$c]);
          return new _A_($UHC.$Base.$ioFromPrim,[$__]);});
$UHC.$OldIO.$hPutStrLn=
 new _F_(function($h,$s)
         {var $__=
           new _A_($UHC.$OldIO.$hPutChar,[$h,10]);
          var $__4=
           new _A_($UHC.$OldIO.$hPutStr,[$h,$s]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__4,$__]);});
$UHC.$OldIO.$putStrLn=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$OldIO.$hPutStrLn,[$UHC.$OldIO.$stdout]);}),[]);
$UHC.$Base.$primExitWith=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return primExitWith($__2);});
$UHC.$Base.$__78__1289__0=
 new _F_(function($e,$__)
         {return new _A_($UHC.$Base.$primExitWith,[$e]);});
$UHC.$Base.$ioFromPrim=
 new _F_(function($f,$w)
         {var $x=
           new _A_($f,[$w]);
          var $x4=
           _e_($x);
          return [$w,$x];});
$UHC.$Base.$exitWithIntCode=
 new _F_(function($e)
         {var $__=
           new _A_($UHC.$Base.$__78__1289__0,[$e]);
          return new _A_($UHC.$Base.$ioFromPrim,[$__]);});
$UHC.$Run.$__276__5__0=
 new _F_(function($exc)
         {var $__=
           new _A_($UHC.$Base.$exitWithIntCode,[1]);
          var $__3=
           new _A_($UHC.$Base.$show,[$UHC.$IOBase.$Show__DCT230__21__0,$exc]);
          var $__4=
           new _A_($UHC.$Base.$packedStringToString,["Error: "]);
          var $__5=
           new _A_($UHC.$Base.$_2b_2b,[$__4,$__3]);
          var $__6=
           new _A_($UHC.$OldIO.$putStrLn,[$__5]);
          var $__7=
           new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__6,$__]);
          var $__8=
           _e_($exc);
          var $__swJSW24__0;
          switch($__8._tag_)
           {case 0:
             $__swJSW24__0=
              $__7;
             break;
            case 1:
             $__swJSW24__0=
              $__7;
             break;
            case 2:
             $__swJSW24__0=
              $__7;
             break;
            case 3:
             $__swJSW24__0=
              $__7;
             break;
            case 4:
             $__swJSW24__0=
              $__7;
             break;
            case 5:
             $__swJSW24__0=
              $__7;
             break;
            case 6:
             $__swJSW24__0=
              $__7;
             break;
            case 7:
             var $__15=
              _e_($__8._1);
             var $__swJSW25__0;
             switch($__15._tag_)
              {case 0:
                var $__17=
                 new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__88__0,$__15._1,0]);
                var $__18=
                 _e_($__17);
                var $__swJSW26__0;
                switch($__18._tag_)
                 {case 0:
                   var $__19=
                    _e_($UHC.$Base.$otherwise);
                   var $__swJSW27__0;
                   switch($__19._tag_)
                    {case 0:
                      $__swJSW27__0=
                       $__7;
                      break;
                     case 1:
                      var $__20=
                       new _A_($UHC.$Base.$exitWithIntCode,[$__15._1]);
                      $__swJSW27__0=
                       $__20;
                      break;}
                   $__swJSW26__0=
                    $__swJSW27__0;
                   break;
                  case 1:
                   var $__21=
                    new _A_($UHC.$Base.$exitWithIntCode,[1]);
                   $__swJSW26__0=
                    $__21;
                   break;}
                $__swJSW25__0=
                 $__swJSW26__0;
                break;
               case 1:
                var $__22=
                 new _A_($UHC.$Base.$exitWithIntCode,[0]);
                $__swJSW25__0=
                 $__22;
                break;}
             $__swJSW24__0=
              $__swJSW25__0;
             break;
            case 8:
             $__swJSW24__0=
              $__7;
             break;
            case 9:
             $__swJSW24__0=
              $__7;
             break;
            case 10:
             $__swJSW24__0=
              $__7;
             break;
            case 11:
             $__swJSW24__0=
              $__7;
             break;
            case 12:
             $__swJSW24__0=
              $__7;
             break;
            case 13:
             $__swJSW24__0=
              $__7;
             break;
            case 14:
             $__swJSW24__0=
              $__7;
             break;}
          return $__swJSW24__0;});
$UHC.$Base.$IO__=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$id;}),[]);
$UHC.$IOBase.$primCatchException=
 new _F_(function($__,$__2)
         {return primCatchException($__,$__2);});
$UHC.$IOBase.$__234__2948__0=
 new _F_(function($k,$s,$te)
         {var $__=
           new _A_($k,[$te]);
          return new _A_($__,[$s]);});
$UHC.$IOBase.$__234__2943__0=
 new _F_(function($__,$k,$s)
         {var $__4=
           new _A_($__,[$s]);
          var $__5=
           new _A_($UHC.$IOBase.$__234__2948__0,[$k,$s]);
          return new _A_($UHC.$IOBase.$primCatchException,[$__4,$__5]);});
$UHC.$IOBase.$catchException=
 new _F_(function($__,$k)
         {var $__3=
           new _A_($UHC.$IOBase.$__234__2943__0,[$__,$k]);
          return new _A_($UHC.$Base.$_24,[$UHC.$Base.$IO__,$__3]);});
$UHC.$Run.$ehcRunMain=
 new _F_(function($m)
         {return new _A_($UHC.$IOBase.$catchException,[$m,$UHC.$Run.$__276__5__0]);});
$JCU.$__42__1264__2__0=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Show__DCT74__87__0,[$Language.$Prolog.$NanoProlog.$NanoProlog.$Show__DCT52__15__0]);}),[]);
$Util.$readMaybe=
 new _F_(function($__,$s)
         {var $__3=
           new _A_($UHC.$Base.$reads,[$__,$s]);
          var $__4=
           _e_($__3);
          var $__swJSW28__0;
          switch($__4._tag_)
           {case 0:
             var $__7=
              _e_($__4._1);
             var $__10=
              _e_($__7[1]);
             var $__swJSW30__0;
             switch($__10._tag_)
              {case 0:
                $__swJSW30__0=
                 $UHC.$Base.$Nothing__;
                break;
               case 1:
                var $__13=
                 _e_($__4._2);
                var $__swJSW31__0;
                switch($__13._tag_)
                 {case 0:
                   $__swJSW31__0=
                    $UHC.$Base.$Nothing__;
                   break;
                  case 1:
                   var $__16=
                    new _A_($UHC.$Base.$Just__,[$__7[0]]);
                   $__swJSW31__0=
                    $__16;
                   break;}
                $__swJSW30__0=
                 $__swJSW31__0;
                break;}
             $__swJSW28__0=
              $__swJSW30__0;
             break;
            case 1:
             $__swJSW28__0=
              $UHC.$Base.$Nothing__;
             break;}
          return $__swJSW28__0;});
$Data.$LocalStorage.$lengthLocalStorage=
 new _F_(function($__)
         {var $__2=
           _e_(localStorage.length);
          return [$__,$__2];});
$Data.$LocalStorage.$__50__244=
 new _A_(new _F_(function()
                 {return new _A_($Language.$UHC.$JS.$Types.$fromJS,[$Language.$UHC.$JS.$ECMA.$String.$FromJS__DCT40__4__0]);}),[]);
$Data.$LocalStorage.$__50__242=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$fmap,[$UHC.$Base.$Functor__DCT74__338__0,$Data.$LocalStorage.$__50__244]);}),[]);
$Data.$LocalStorage.$__keyLocalStorage=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_(localStorage.key($__3));
          return [$__2,$__4];});
$Data.$LocalStorage.$keyLocalStorage=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_2e,[$Data.$LocalStorage.$__50__242,$Data.$LocalStorage.$__keyLocalStorage]);}),[]);
$Data.$LocalStorage.$_24okUNQ266=
 new _F_(function($_24x,$_24x2)
         {var $__=
           new _A_($UHC.$Base.$_3a,[$_24x,$_24x2]);
          var $__4=
           new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0]);
          return new _A_($UHC.$Base.$_24,[$__4,$__]);});
$Data.$LocalStorage.$_24okUNQ262=
 new _F_(function($i,$m,$_24x)
         {var $__=
           new _A_($UHC.$Base.$_2b,[$UHC.$Base.$Num__DCT74__101__0,$i,1]);
          var $__5=
           new _A_($Data.$LocalStorage.$iterateUNQ243,[$__,$m]);
          var $__6=
           new _A_($Data.$LocalStorage.$_24okUNQ266,[$_24x]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__5,$__6]);});
$Data.$LocalStorage.$iterateUNQ243=
 new _F_(function($i,$m)
         {var $__=
           new _A_($UHC.$Base.$_3c,[$UHC.$Base.$Ord__DCT74__91__0,$i,$m]);
          var $__4=
           _e_($__);
          var $__swJSW32__0;
          switch($__4._tag_)
           {case 0:
             var $__5=
              new _A_($UHC.$Base.$_3e_3d,[$UHC.$Base.$Ord__DCT74__91__0,$i,$m]);
             var $__6=
              _e_($__5);
             var $__swJSW33__0;
             switch($__6._tag_)
              {case 0:
                var $__7=
                 new _A_($UHC.$Base.$packedStringToString,["FAIL 47_6_0"]);
                var $__8=
                 new _A_($UHC.$Base.$error,[$__7]);
                $__swJSW33__0=
                 $__8;
                break;
               case 1:
                var $__9=
                 new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0,$UHC.$Base.$_5b_5d]);
                $__swJSW33__0=
                 $__9;
                break;}
             $__swJSW32__0=
              $__swJSW33__0;
             break;
            case 1:
             var $__10=
              new _A_($Data.$LocalStorage.$keyLocalStorage,[$i]);
             var $__11=
              new _A_($Data.$LocalStorage.$_24okUNQ262,[$i,$m]);
             $__swJSW32__0=
              new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__10,$__11]);
             break;}
          return $__swJSW32__0;});
$Data.$LocalStorage.$_24okUNQ275=
 new _F_(function($key,$__,$_24x)
         {var $__4=
           new _A_($UHC.$Base.$elem,[$__,$key,$_24x]);
          var $__5=
           new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0]);
          return new _A_($UHC.$Base.$_24,[$__5,$__4]);});
$Data.$LocalStorage.$_24okUNQ249=
 new _F_(function($key,$_24x)
         {var $__=
           new _A_($UHC.$Base.$Eq__DCT74__394__0,[$UHC.$Base.$Eq__DCT74__56__0]);
          var $__4=
           new _A_($Data.$LocalStorage.$iterateUNQ243,[0,$_24x]);
          var $__5=
           new _A_($Data.$LocalStorage.$_24okUNQ275,[$key,$__]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__4,$__5]);});
$Data.$LocalStorage.$keyExistsInLocalStorage=
 new _F_(function($key)
         {var $__=
           new _A_($Data.$LocalStorage.$_24okUNQ249,[$key]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$Data.$LocalStorage.$lengthLocalStorage,$__]);});
$Control.$Monad.$unless=
 new _F_(function($__,$p,$s)
         {var $__4=
           _e_($p);
          var $__swJSW34__0;
          switch($__4._tag_)
           {case 0:
             $__swJSW34__0=
              $s;
             break;
            case 1:
             var $__5=
              new _A_($UHC.$Base.$return,[$__,[]]);
             $__swJSW34__0=
              $__5;
             break;}
          return $__swJSW34__0;});
$JCU.$_24okUNQ182=
 new _F_(function($__,$def,$key,$p,$_24x)
         {var $__6=
           new _A_($Data.$LocalStorage.$setLocalStorage,[$__,$key,$def]);
          var $__7=
           new _A_($p,[$_24x]);
          var $__8=
           new _A_($Control.$Monad.$unless,[$UHC.$Base.$Monad__DCT74__339__0,$__7]);
          return new _A_($UHC.$Base.$_24,[$__8,$__6]);});
$Util.$fromJSString=
 new _A_(new _F_(function()
                 {return new _A_($Language.$UHC.$JS.$Types.$fromJS,[$Language.$UHC.$JS.$ECMA.$String.$FromJS__DCT40__4__0]);}),[]);
$JCU.$_24okUNQ174=
 new _F_(function($__,$def,$key,$p,$_24x)
         {var $__6=
           _e_($_24x);
          var $__swJSW35__0;
          switch($__6._tag_)
           {case 0:
             var $__7=
              new _A_($Data.$LocalStorage.$setLocalStorage,[$__,$key,$def]);
             $__swJSW35__0=
              $__7;
             break;
            case 1:
             var $__8=
              new _A_($Language.$UHC.$JS.$Types.$toJS,[$Language.$UHC.$JS.$ECMA.$String.$ToJS__DCT40__2__0,$key]);
             var $__9=
              new _A_($Data.$LocalStorage.$__getLocalStorage,[$__8]);
             var $__10=
              new _A_($UHC.$Base.$fmap,[$UHC.$Base.$Functor__DCT74__338__0,$Util.$fromJSString,$__9]);
             var $__11=
              new _A_($JCU.$_24okUNQ182,[$__,$def,$key,$p]);
             $__swJSW35__0=
              new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__10,$__11]);
             break;}
          return $__swJSW35__0;});
$JCU.$checkUNQ149=
 new _F_(function($__,$__2,$__3)
         {var $__4=
           _e_($__3);
          var $__8=
           new _A_($Data.$LocalStorage.$keyExistsInLocalStorage,[$__4[0]]);
          var $__9=
           new _A_($JCU.$_24okUNQ174,[$__,$__4[1],$__4[0],$__4[2]]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__8,$__9]);});
$Util.$isJust=
 new _F_(function($x1)
         {var $__=
           _e_($x1);
          var $__swJSW37__0;
          switch($__._tag_)
           {case 0:
             $__swJSW37__0=
              $UHC.$Base.$True__;
             break;
            case 1:
             $__swJSW37__0=
              $UHC.$Base.$False__;
             break;}
          return $__swJSW37__0;});
$JCU.$__42__1264__5__0=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Read__DCT74__86__0,[$Models.$Read__DCT82__6__0]);}),[]);
$JCU.$initializeApplicationDefaults=
 new _A_(new _F_(function()
                 {var $__=
                   new _A_($Util.$readMaybe,[$UHC.$Base.$__74__51__0]);
                  var $__2=
                   new _A_($UHC.$Base.$_2e,[$Util.$isJust,$__]);
                  var $__3=
                   [$JCU.$checkProofStoreKey,$UHC.$Base.$False__,$__2];
                  var $__4=
                   new _A_($JCU.$checkUNQ149,[$UHC.$Base.$__74__50__0,$UHC.$Base.$__74__51__0,$__3]);
                  var $__5=
                   new _A_($Models.$run,[$Models.$pRules]);
                  var $__6=
                   new _A_($UHC.$Base.$_2e,[$Util.$isJust,$__5]);
                  var $__7=
                   [$JCU.$rulesStoreKey,$UHC.$Base.$_5b_5d,$__6];
                  var $__8=
                   new _A_($JCU.$checkUNQ149,[$JCU.$__42__1264__2__0,$JCU.$__42__1264__5__0,$__7]);
                  return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__8,$__4]);}),[]);
$Language.$UHC.$JS.$JQuery.$JQuery.$__ready=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($("document").ready($__3));
          var $__5=
           _e_([]);
          return [$__2,$__5];});
$Language.$UHC.$JS.$JQuery.$JQuery.$onDocumentReady=
 new _A_(new _F_(function()
                 {return $Language.$UHC.$JS.$JQuery.$JQuery.$__ready;}),[]);
$JCU.$_24okUNQ747=
 new _F_(function($_24x)
         {var $__=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$onDocumentReady,[$_24x]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$JCU.$initializeApplicationDefaults,$__]);});
$Language.$UHC.$JS.$Prelude.$wrapIO=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_(function()
               {var res=
                 _e_(new _A_($__3,[[]]));
                _e_(res[0]);
                return _e_(res[1]);});
          return [$__2,$__4];});
$JCU.$_24okUNQ613=
 new _F_(function($_24x,$_24x2)
         {var $__=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$append,[$_24x,$_24x2]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__,$JCU.$setRulesList]);});
$JCU.$_24okUNQ607=
 new _F_(function($_24x)
         {var $__=
           new _A_($UHC.$Base.$packedStringToString,["<ul id=\"rules-list-view\"/>"]);
          var $__3=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$jQuery,[$__]);
          var $__4=
           new _A_($JCU.$_24okUNQ613,[$_24x]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__3,$__4]);});
$JCU.$addRules=
 new _A_(new _F_(function()
                 {var $__=
                   new _A_($UHC.$Base.$packedStringToString,["#rules-list-div"]);
                  var $__2=
                   new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$jQuery,[$__]);
                  return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__2,$JCU.$_24okUNQ607]);}),[]);
$Prolog.$__32__74=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["Alexander is ouder van Amalia"]);}),[]);
$Prolog.$__32__77=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["ouder"]);}),[]);
$Prolog.$__32__81=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["alex"]);}),[]);
$Prolog.$__32__80=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$cnst,[$Prolog.$__32__81]);}),[]);
$Prolog.$__32__85=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["ama"]);}),[]);
$Prolog.$__32__84=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$cnst,[$Prolog.$__32__85]);}),[]);
$Prolog.$__32__82=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__84,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__78=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__80,$Prolog.$__32__82]);}),[]);
$Prolog.$__32__75=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__77,$Prolog.$__32__78]);}),[]);
$Prolog.$__32__72=
 new _A_(new _F_(function()
                 {return [$Prolog.$__32__74,$Prolog.$__32__75];}),[]);
$Prolog.$__32__106=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["Beatrix is de moeder van iemand"]);}),[]);
$Prolog.$__32__109=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["ouder"]);}),[]);
$Prolog.$__32__113=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["bea"]);}),[]);
$Prolog.$__32__112=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$cnst,[$Prolog.$__32__113]);}),[]);
$Prolog.$__32__117=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["X"]);}),[]);
$Prolog.$__32__116=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__117]);}),[]);
$Prolog.$__32__114=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__116,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__110=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__112,$Prolog.$__32__114]);}),[]);
$Prolog.$__32__107=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__109,$Prolog.$__32__110]);}),[]);
$Prolog.$__32__104=
 new _A_(new _F_(function()
                 {return [$Prolog.$__32__106,$Prolog.$__32__107];}),[]);
$Prolog.$__32__102=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__104,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__90=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["Beatrix is voorouder van Amalia"]);}),[]);
$Prolog.$__32__93=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["voor"]);}),[]);
$Prolog.$__32__101=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["ama"]);}),[]);
$Prolog.$__32__100=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$cnst,[$Prolog.$__32__101]);}),[]);
$Prolog.$__32__98=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__100,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__97=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["bea"]);}),[]);
$Prolog.$__32__96=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$cnst,[$Prolog.$__32__97]);}),[]);
$Prolog.$__32__94=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__96,$Prolog.$__32__98]);}),[]);
$Prolog.$__32__91=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__93,$Prolog.$__32__94]);}),[]);
$Prolog.$__32__88=
 new _A_(new _F_(function()
                 {return [$Prolog.$__32__90,$Prolog.$__32__91];}),[]);
$Prolog.$__32__86=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__88,$Prolog.$__32__102]);}),[]);
$Prolog.$exampleGoals=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__72,$Prolog.$__32__86]);}),[]);
$JCU.$_24okUNQ113=
 new _F_(function($_24x,$_24x2)
         {return new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$append,[$_24x,$_24x2]);});
$JCU.$fUNQ98=
 new _F_(function($_24x,$__,$__3)
         {var $__4=
           _e_($__3);
          var $__7=
           new _A_($UHC.$Base.$packedStringToString,["</option>"]);
          var $__8=
           new _A_($UHC.$Base.$_2b_2b,[$__4[0],$__7]);
          var $__9=
           new _A_($UHC.$Base.$packedStringToString,["\">"]);
          var $__10=
           new _A_($UHC.$Base.$_2b_2b,[$__9,$__8]);
          var $__11=
           new _A_($UHC.$Base.$show,[$__,$__4[1]]);
          var $__12=
           new _A_($UHC.$Base.$_2b_2b,[$__11,$__10]);
          var $__13=
           new _A_($UHC.$Base.$packedStringToString,["<option value=\""]);
          var $__14=
           new _A_($UHC.$Base.$_2b_2b,[$__13,$__12]);
          var $__15=
           new _A_($UHC.$Base.$_24,[$Language.$UHC.$JS.$JQuery.$JQuery.$jQuery,$__14]);
          var $__16=
           new _A_($JCU.$_24okUNQ113,[$_24x]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__15,$__16]);});
$JCU.$__44__16NEW6=
 new _F_(function($_24x)
         {var $__=
           new _A_($JCU.$fUNQ98,[$_24x,$Language.$Prolog.$NanoProlog.$NanoProlog.$Show__DCT52__14__0]);
          return new _A_($UHC.$Base.$mapM__,[$UHC.$Base.$Monad__DCT74__339__0,$__,$Prolog.$exampleGoals]);});
$JCU.$_24okUNQ93=
 new _F_(function($_24x)
         {var $__=
           new _A_($JCU.$__44__16NEW6,[$_24x]);
          var $__3=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$empty,[$_24x]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__3,$__]);});
$JCU.$addExampleGoals=
 new _A_(new _F_(function()
                 {var $__=
                   new _A_($UHC.$Base.$packedStringToString,["#startTerm"]);
                  var $__2=
                   new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$jQuery,[$__]);
                  return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__2,$JCU.$_24okUNQ93]);}),[]);
$JCU.$clearRules=
 new _F_(function($__)
         {var $__2=
           new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0,$UHC.$Base.$False__]);
          var $__3=
           new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$JCU.$setRulesList,$__2]);
          var $__4=
           new _A_($JCU.$writeRulesInStore,[$UHC.$Base.$_5b_5d]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__4,$__3]);});
$Prolog.$__32__157=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["ama"]);}),[]);
$Prolog.$__32__155=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__157,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__154=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["alex"]);}),[]);
$Prolog.$__32__152=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__154,$Prolog.$__32__155]);}),[]);
$Prolog.$__32__151=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$paFact,[$Prolog.$__32__152]);}),[]);
$Prolog.$__32__175=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["ari"]);}),[]);
$Prolog.$__32__173=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__175,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__172=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["alex"]);}),[]);
$Prolog.$__32__170=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__172,$Prolog.$__32__173]);}),[]);
$Prolog.$__32__169=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$paFact,[$Prolog.$__32__170]);}),[]);
$Prolog.$__32__181=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["claus"]);}),[]);
$Prolog.$__32__184=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["alex"]);}),[]);
$Prolog.$__32__182=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__184,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__179=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__181,$Prolog.$__32__182]);}),[]);
$Prolog.$__32__178=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$paFact,[$Prolog.$__32__179]);}),[]);
$Prolog.$__32__193=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["const"]);}),[]);
$Prolog.$__32__191=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__193,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__190=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["claus"]);}),[]);
$Prolog.$__32__188=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__190,$Prolog.$__32__191]);}),[]);
$Prolog.$__32__187=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$paFact,[$Prolog.$__32__188]);}),[]);
$Prolog.$__32__199=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["claus"]);}),[]);
$Prolog.$__32__202=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["friso"]);}),[]);
$Prolog.$__32__200=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__202,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__197=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__199,$Prolog.$__32__200]);}),[]);
$Prolog.$__32__196=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$paFact,[$Prolog.$__32__197]);}),[]);
$Prolog.$__32__229=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["ari"]);}),[]);
$Prolog.$__32__227=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__229,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__226=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["max"]);}),[]);
$Prolog.$__32__224=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__226,$Prolog.$__32__227]);}),[]);
$Prolog.$__32__223=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$maFact,[$Prolog.$__32__224]);}),[]);
$Prolog.$__32__274=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["juul"]);}),[]);
$Prolog.$__32__272=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__274,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__271=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["mien"]);}),[]);
$Prolog.$__32__269=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__271,$Prolog.$__32__272]);}),[]);
$Prolog.$__32__268=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$maFact,[$Prolog.$__32__269]);}),[]);
$Prolog.$__32__309=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["ouder"]);}),[]);
$Prolog.$__32__317=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["Y"]);}),[]);
$Prolog.$__32__316=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__317]);}),[]);
$Prolog.$__32__314=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__316,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__313=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["X"]);}),[]);
$Prolog.$__32__312=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__313]);}),[]);
$Prolog.$__32__310=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__312,$Prolog.$__32__314]);}),[]);
$Prolog.$__32__307=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__309,$Prolog.$__32__310]);}),[]);
$Prolog.$__32__322=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["ma"]);}),[]);
$Prolog.$__32__326=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["X"]);}),[]);
$Prolog.$__32__325=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__326]);}),[]);
$Prolog.$__32__330=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["Y"]);}),[]);
$Prolog.$__32__329=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__330]);}),[]);
$Prolog.$__32__327=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__329,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__323=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__325,$Prolog.$__32__327]);}),[]);
$Prolog.$__32__320=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__322,$Prolog.$__32__323]);}),[]);
$Prolog.$__32__318=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__320,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__305=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$_3a_3c_2d_3a,[$Prolog.$__32__307,$Prolog.$__32__318]);}),[]);
$Prolog.$__32__397=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["X"]);}),[]);
$Prolog.$__32__396=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__397]);}),[]);
$Prolog.$__32__401=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["Y"]);}),[]);
$Prolog.$__32__400=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__401]);}),[]);
$Prolog.$__32__398=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__400,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__394=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__396,$Prolog.$__32__398]);}),[]);
$Prolog.$__32__393=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["voor"]);}),[]);
$Prolog.$__32__391=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__393,$Prolog.$__32__394]);}),[]);
$Prolog.$__32__419=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["voor"]);}),[]);
$Prolog.$__32__423=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["X"]);}),[]);
$Prolog.$__32__422=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__423]);}),[]);
$Prolog.$__32__427=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["Z"]);}),[]);
$Prolog.$__32__426=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__427]);}),[]);
$Prolog.$__32__424=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__426,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__420=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__422,$Prolog.$__32__424]);}),[]);
$Prolog.$__32__417=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__419,$Prolog.$__32__420]);}),[]);
$Prolog.$__32__415=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__417,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__414=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["Y"]);}),[]);
$Prolog.$__32__413=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__414]);}),[]);
$Prolog.$__32__411=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__413,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__410=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["Z"]);}),[]);
$Prolog.$__32__409=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__410]);}),[]);
$Prolog.$__32__407=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__409,$Prolog.$__32__411]);}),[]);
$Prolog.$__32__406=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["ouder"]);}),[]);
$Prolog.$__32__404=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__406,$Prolog.$__32__407]);}),[]);
$Prolog.$__32__402=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__404,$Prolog.$__32__415]);}),[]);
$Prolog.$__32__389=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$_3a_3c_2d_3a,[$Prolog.$__32__391,$Prolog.$__32__402]);}),[]);
$Prolog.$__32__443=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["oeps"]);}),[]);
$Prolog.$__32__447=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["Y"]);}),[]);
$Prolog.$__32__446=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__447]);}),[]);
$Prolog.$__32__444=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__446,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__441=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__443,$Prolog.$__32__444]);}),[]);
$Prolog.$__32__439=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__441,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__434=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["oeps"]);}),[]);
$Prolog.$__32__438=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["X"]);}),[]);
$Prolog.$__32__437=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__438]);}),[]);
$Prolog.$__32__435=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__437,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__432=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__434,$Prolog.$__32__435]);}),[]);
$Prolog.$__32__430=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$_3a_3c_2d_3a,[$Prolog.$__32__432,$Prolog.$__32__439]);}),[]);
$Prolog.$__32__452=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["plus"]);}),[]);
$Prolog.$__32__460=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["X"]);}),[]);
$Prolog.$__32__459=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__460]);}),[]);
$Prolog.$__32__464=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["X"]);}),[]);
$Prolog.$__32__463=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__464]);}),[]);
$Prolog.$__32__461=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__463,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__457=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__459,$Prolog.$__32__461]);}),[]);
$Prolog.$__32__456=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["zero"]);}),[]);
$Prolog.$__32__455=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$cnst,[$Prolog.$__32__456]);}),[]);
$Prolog.$__32__453=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__455,$Prolog.$__32__457]);}),[]);
$Prolog.$__32__450=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$fact,[$Prolog.$__32__452,$Prolog.$__32__453]);}),[]);
$Prolog.$__32__521=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["zero"]);}),[]);
$Prolog.$__32__520=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$cnst,[$Prolog.$__32__521]);}),[]);
$Prolog.$__32__518=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__520,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__516=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$nil,$Prolog.$__32__518]);}),[]);
$Prolog.$__32__515=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["length"]);}),[]);
$Prolog.$__32__513=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$fact,[$Prolog.$__32__515,$Prolog.$__32__516]);}),[]);
$Prolog.$__32__672=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["verschillend"]);}),[]);
$Prolog.$__32__676=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["XS"]);}),[]);
$Prolog.$__32__675=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__676]);}),[]);
$Prolog.$__32__673=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__675,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__670=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__672,$Prolog.$__32__673]);}),[]);
$Prolog.$__32__685=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["XSS"]);}),[]);
$Prolog.$__32__684=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__685]);}),[]);
$Prolog.$__32__682=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__684,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__681=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["juist"]);}),[]);
$Prolog.$__32__679=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__681,$Prolog.$__32__682]);}),[]);
$Prolog.$__32__677=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__679,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__668=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__670,$Prolog.$__32__677]);}),[]);
$Prolog.$__32__654=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["juist"]);}),[]);
$Prolog.$__32__667=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["XSS"]);}),[]);
$Prolog.$__32__666=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__667]);}),[]);
$Prolog.$__32__664=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__666,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__663=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["XS"]);}),[]);
$Prolog.$__32__662=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__663]);}),[]);
$Prolog.$__32__660=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__662,$Prolog.$__32__664]);}),[]);
$Prolog.$__32__659=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["cons"]);}),[]);
$Prolog.$__32__657=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__659,$Prolog.$__32__660]);}),[]);
$Prolog.$__32__655=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__657,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__652=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__654,$Prolog.$__32__655]);}),[]);
$Prolog.$__32__650=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$_3a_3c_2d_3a,[$Prolog.$__32__652,$Prolog.$__32__668]);}),[]);
$Prolog.$__32__717=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["cons"]);}),[]);
$Prolog.$__32__724=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["cons"]);}),[]);
$Prolog.$__32__734=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$nil,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__732=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$nil,$Prolog.$__32__734]);}),[]);
$Prolog.$__32__731=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["cons"]);}),[]);
$Prolog.$__32__729=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__731,$Prolog.$__32__732]);}),[]);
$Prolog.$__32__727=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__729,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__725=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$nil,$Prolog.$__32__727]);}),[]);
$Prolog.$__32__722=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__724,$Prolog.$__32__725]);}),[]);
$Prolog.$__32__720=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__722,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__718=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$nil,$Prolog.$__32__720]);}),[]);
$Prolog.$__32__715=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__717,$Prolog.$__32__718]);}),[]);
$Prolog.$__32__713=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__715,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__711=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$nil,$Prolog.$__32__713]);}),[]);
$Prolog.$__32__710=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["cons"]);}),[]);
$Prolog.$__32__708=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__710,$Prolog.$__32__711]);}),[]);
$Prolog.$__32__706=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__708,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__704=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$nil,$Prolog.$__32__706]);}),[]);
$Prolog.$__32__703=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["kolommen"]);}),[]);
$Prolog.$__32__701=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$fact,[$Prolog.$__32__703,$Prolog.$__32__704]);}),[]);
$Prolog.$__32__742=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["kolommen"]);}),[]);
$Prolog.$__32__747=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["cons"]);}),[]);
$Prolog.$__32__751=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["XS"]);}),[]);
$Prolog.$__32__750=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__751]);}),[]);
$Prolog.$__32__755=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["XSS"]);}),[]);
$Prolog.$__32__754=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__755]);}),[]);
$Prolog.$__32__752=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__754,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__748=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__750,$Prolog.$__32__752]);}),[]);
$Prolog.$__32__745=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__747,$Prolog.$__32__748]);}),[]);
$Prolog.$__32__743=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__745,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__740=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__742,$Prolog.$__32__743]);}),[]);
$Prolog.$__32__760=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["voegtoe"]);}),[]);
$Prolog.$__32__764=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["XS"]);}),[]);
$Prolog.$__32__763=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__764]);}),[]);
$Prolog.$__32__772=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["ZSS"]);}),[]);
$Prolog.$__32__771=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__772]);}),[]);
$Prolog.$__32__769=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__771,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__768=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["YSS"]);}),[]);
$Prolog.$__32__767=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__768]);}),[]);
$Prolog.$__32__765=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__767,$Prolog.$__32__769]);}),[]);
$Prolog.$__32__761=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__763,$Prolog.$__32__765]);}),[]);
$Prolog.$__32__758=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__760,$Prolog.$__32__761]);}),[]);
$Prolog.$__32__785=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["YSS"]);}),[]);
$Prolog.$__32__784=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__785]);}),[]);
$Prolog.$__32__782=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__784,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__781=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["XSS"]);}),[]);
$Prolog.$__32__780=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__781]);}),[]);
$Prolog.$__32__778=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__780,$Prolog.$__32__782]);}),[]);
$Prolog.$__32__777=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["kolommen"]);}),[]);
$Prolog.$__32__775=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__777,$Prolog.$__32__778]);}),[]);
$Prolog.$__32__773=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__775,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__756=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__758,$Prolog.$__32__773]);}),[]);
$Prolog.$__32__738=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$_3a_3c_2d_3a,[$Prolog.$__32__740,$Prolog.$__32__756]);}),[]);
$Prolog.$__32__795=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$nil,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__793=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$nil,$Prolog.$__32__795]);}),[]);
$Prolog.$__32__791=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$nil,$Prolog.$__32__793]);}),[]);
$Prolog.$__32__790=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["voegtoe"]);}),[]);
$Prolog.$__32__788=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$fact,[$Prolog.$__32__790,$Prolog.$__32__791]);}),[]);
$Prolog.$__32__856=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["voegtoe"]);}),[]);
$Prolog.$__32__860=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["XS"]);}),[]);
$Prolog.$__32__859=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__860]);}),[]);
$Prolog.$__32__864=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["YSS"]);}),[]);
$Prolog.$__32__863=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__864]);}),[]);
$Prolog.$__32__868=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["ZSS"]);}),[]);
$Prolog.$__32__867=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__868]);}),[]);
$Prolog.$__32__865=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__867,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__861=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__863,$Prolog.$__32__865]);}),[]);
$Prolog.$__32__857=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__859,$Prolog.$__32__861]);}),[]);
$Prolog.$__32__854=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__856,$Prolog.$__32__857]);}),[]);
$Prolog.$__32__852=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__854,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__803=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["voegtoe"]);}),[]);
$Prolog.$__32__829=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["YSS"]);}),[]);
$Prolog.$__32__828=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__829]);}),[]);
$Prolog.$__32__826=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__828,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__825=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["YS"]);}),[]);
$Prolog.$__32__824=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__825]);}),[]);
$Prolog.$__32__822=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__824,$Prolog.$__32__826]);}),[]);
$Prolog.$__32__821=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["cons"]);}),[]);
$Prolog.$__32__819=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__821,$Prolog.$__32__822]);}),[]);
$Prolog.$__32__834=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["cons"]);}),[]);
$Prolog.$__32__851=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["ZSS"]);}),[]);
$Prolog.$__32__850=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__851]);}),[]);
$Prolog.$__32__848=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__850,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__847=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["YS"]);}),[]);
$Prolog.$__32__846=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__847]);}),[]);
$Prolog.$__32__844=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__846,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__843=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["X"]);}),[]);
$Prolog.$__32__842=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__843]);}),[]);
$Prolog.$__32__840=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__842,$Prolog.$__32__844]);}),[]);
$Prolog.$__32__839=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["cons"]);}),[]);
$Prolog.$__32__837=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__839,$Prolog.$__32__840]);}),[]);
$Prolog.$__32__835=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__837,$Prolog.$__32__848]);}),[]);
$Prolog.$__32__832=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__834,$Prolog.$__32__835]);}),[]);
$Prolog.$__32__830=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__832,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__817=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__819,$Prolog.$__32__830]);}),[]);
$Prolog.$__32__816=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["XS"]);}),[]);
$Prolog.$__32__815=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__816]);}),[]);
$Prolog.$__32__813=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__815,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__812=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["X"]);}),[]);
$Prolog.$__32__811=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__812]);}),[]);
$Prolog.$__32__809=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__811,$Prolog.$__32__813]);}),[]);
$Prolog.$__32__808=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["cons"]);}),[]);
$Prolog.$__32__806=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__808,$Prolog.$__32__809]);}),[]);
$Prolog.$__32__804=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__806,$Prolog.$__32__817]);}),[]);
$Prolog.$__32__801=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__803,$Prolog.$__32__804]);}),[]);
$Prolog.$__32__799=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$_3a_3c_2d_3a,[$Prolog.$__32__801,$Prolog.$__32__852]);}),[]);
$Prolog.$__32__797=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__799,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__786=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__788,$Prolog.$__32__797]);}),[]);
$Prolog.$__32__736=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__738,$Prolog.$__32__786]);}),[]);
$Prolog.$__32__699=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__701,$Prolog.$__32__736]);}),[]);
$Prolog.$__32__690=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["rijen"]);}),[]);
$Prolog.$__32__698=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["XSS"]);}),[]);
$Prolog.$__32__697=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__698]);}),[]);
$Prolog.$__32__695=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__697,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__694=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["XSS"]);}),[]);
$Prolog.$__32__693=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__694]);}),[]);
$Prolog.$__32__691=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__693,$Prolog.$__32__695]);}),[]);
$Prolog.$__32__688=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$fact,[$Prolog.$__32__690,$Prolog.$__32__691]);}),[]);
$Prolog.$__32__686=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__688,$Prolog.$__32__699]);}),[]);
$Prolog.$__32__648=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__650,$Prolog.$__32__686]);}),[]);
$Prolog.$__32__68=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["nil"]);}),[]);
$Prolog.$nil=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$cnst,[$Prolog.$__32__68]);}),[]);
$Prolog.$__32__646=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$nil,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__645=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["juist"]);}),[]);
$Prolog.$__32__643=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$fact,[$Prolog.$__32__645,$Prolog.$__32__646]);}),[]);
$Prolog.$__32__641=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__643,$Prolog.$__32__648]);}),[]);
$Prolog.$__32__574=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["BORD"]);}),[]);
$Prolog.$__32__573=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__574]);}),[]);
$Prolog.$__32__571=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__573,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__570=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["oplossing"]);}),[]);
$Prolog.$__32__568=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__570,$Prolog.$__32__571]);}),[]);
$Prolog.$__32__614=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["juist"]);}),[]);
$Prolog.$__32__618=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["YSS"]);}),[]);
$Prolog.$__32__617=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__618]);}),[]);
$Prolog.$__32__615=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__617,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__612=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__614,$Prolog.$__32__615]);}),[]);
$Prolog.$__32__623=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["vierkanten"]);}),[]);
$Prolog.$__32__627=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["BORD"]);}),[]);
$Prolog.$__32__626=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__627]);}),[]);
$Prolog.$__32__631=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["ZSS"]);}),[]);
$Prolog.$__32__630=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__631]);}),[]);
$Prolog.$__32__628=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__630,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__624=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__626,$Prolog.$__32__628]);}),[]);
$Prolog.$__32__621=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__623,$Prolog.$__32__624]);}),[]);
$Prolog.$__32__636=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["juist"]);}),[]);
$Prolog.$__32__640=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["ZSS"]);}),[]);
$Prolog.$__32__639=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__640]);}),[]);
$Prolog.$__32__637=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__639,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__634=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__636,$Prolog.$__32__637]);}),[]);
$Prolog.$__32__632=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__634,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__619=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__621,$Prolog.$__32__632]);}),[]);
$Prolog.$__32__610=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__612,$Prolog.$__32__619]);}),[]);
$Prolog.$__32__609=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["YSS"]);}),[]);
$Prolog.$__32__608=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__609]);}),[]);
$Prolog.$__32__606=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__608,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__605=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["BORD"]);}),[]);
$Prolog.$__32__604=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__605]);}),[]);
$Prolog.$__32__602=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__604,$Prolog.$__32__606]);}),[]);
$Prolog.$__32__601=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["kolommen"]);}),[]);
$Prolog.$__32__599=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__601,$Prolog.$__32__602]);}),[]);
$Prolog.$__32__597=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__599,$Prolog.$__32__610]);}),[]);
$Prolog.$__32__596=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["XSS"]);}),[]);
$Prolog.$__32__595=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__596]);}),[]);
$Prolog.$__32__593=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__595,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__592=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["juist"]);}),[]);
$Prolog.$__32__590=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__592,$Prolog.$__32__593]);}),[]);
$Prolog.$__32__588=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__590,$Prolog.$__32__597]);}),[]);
$Prolog.$__32__587=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["XSS"]);}),[]);
$Prolog.$__32__586=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__587]);}),[]);
$Prolog.$__32__584=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__586,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__583=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["BORD"]);}),[]);
$Prolog.$__32__582=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__583]);}),[]);
$Prolog.$__32__580=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__582,$Prolog.$__32__584]);}),[]);
$Prolog.$__32__579=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["rijen"]);}),[]);
$Prolog.$__32__577=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__579,$Prolog.$__32__580]);}),[]);
$Prolog.$__32__575=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__577,$Prolog.$__32__588]);}),[]);
$Prolog.$__32__566=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$_3a_3c_2d_3a,[$Prolog.$__32__568,$Prolog.$__32__575]);}),[]);
$Prolog.$__32__564=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__566,$Prolog.$__32__641]);}),[]);
$Prolog.$__32__559=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["XS"]);}),[]);
$Prolog.$__32__558=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__559]);}),[]);
$Prolog.$__32__563=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["Y"]);}),[]);
$Prolog.$__32__562=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__563]);}),[]);
$Prolog.$__32__560=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__562,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__556=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__558,$Prolog.$__32__560]);}),[]);
$Prolog.$__32__555=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["length"]);}),[]);
$Prolog.$__32__553=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__555,$Prolog.$__32__556]);}),[]);
$Prolog.$__32__551=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__553,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__528=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["length"]);}),[]);
$Prolog.$__32__546=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["succ"]);}),[]);
$Prolog.$__32__550=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["Y"]);}),[]);
$Prolog.$__32__549=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__550]);}),[]);
$Prolog.$__32__547=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__549,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__544=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__546,$Prolog.$__32__547]);}),[]);
$Prolog.$__32__542=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__544,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__533=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["cons"]);}),[]);
$Prolog.$__32__541=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["XS"]);}),[]);
$Prolog.$__32__540=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__541]);}),[]);
$Prolog.$__32__538=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__540,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__537=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["X"]);}),[]);
$Prolog.$__32__536=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__537]);}),[]);
$Prolog.$__32__534=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__536,$Prolog.$__32__538]);}),[]);
$Prolog.$__32__531=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__533,$Prolog.$__32__534]);}),[]);
$Prolog.$__32__529=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__531,$Prolog.$__32__542]);}),[]);
$Prolog.$__32__526=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__528,$Prolog.$__32__529]);}),[]);
$Prolog.$__32__524=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$_3a_3c_2d_3a,[$Prolog.$__32__526,$Prolog.$__32__551]);}),[]);
$Prolog.$__32__522=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__524,$Prolog.$__32__564]);}),[]);
$Prolog.$__32__511=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__513,$Prolog.$__32__522]);}),[]);
$Prolog.$__32__471=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["plus"]);}),[]);
$Prolog.$__32__476=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["succ"]);}),[]);
$Prolog.$__32__480=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["X"]);}),[]);
$Prolog.$__32__479=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__480]);}),[]);
$Prolog.$__32__477=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__479,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__474=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__476,$Prolog.$__32__477]);}),[]);
$Prolog.$__32__493=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["Z"]);}),[]);
$Prolog.$__32__492=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__493]);}),[]);
$Prolog.$__32__490=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__492,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__489=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["succ"]);}),[]);
$Prolog.$__32__487=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__489,$Prolog.$__32__490]);}),[]);
$Prolog.$__32__485=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__487,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__484=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["Y"]);}),[]);
$Prolog.$__32__483=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__484]);}),[]);
$Prolog.$__32__481=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__483,$Prolog.$__32__485]);}),[]);
$Prolog.$__32__472=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__474,$Prolog.$__32__481]);}),[]);
$Prolog.$__32__469=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__471,$Prolog.$__32__472]);}),[]);
$Prolog.$__32__498=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["plus"]);}),[]);
$Prolog.$__32__502=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["X"]);}),[]);
$Prolog.$__32__501=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__502]);}),[]);
$Prolog.$__32__506=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["Y"]);}),[]);
$Prolog.$__32__505=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__506]);}),[]);
$Prolog.$__32__510=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["Z"]);}),[]);
$Prolog.$__32__509=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__510]);}),[]);
$Prolog.$__32__507=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__509,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__503=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__505,$Prolog.$__32__507]);}),[]);
$Prolog.$__32__499=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__501,$Prolog.$__32__503]);}),[]);
$Prolog.$__32__496=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__498,$Prolog.$__32__499]);}),[]);
$Prolog.$__32__494=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__496,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__467=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$_3a_3c_2d_3a,[$Prolog.$__32__469,$Prolog.$__32__494]);}),[]);
$Prolog.$__32__465=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__467,$Prolog.$__32__511]);}),[]);
$Prolog.$__32__448=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__450,$Prolog.$__32__465]);}),[]);
$Prolog.$__32__428=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__430,$Prolog.$__32__448]);}),[]);
$Prolog.$__32__387=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__389,$Prolog.$__32__428]);}),[]);
$Prolog.$__32__365=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["voor"]);}),[]);
$Prolog.$__32__369=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["X"]);}),[]);
$Prolog.$__32__368=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__369]);}),[]);
$Prolog.$__32__373=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["Y"]);}),[]);
$Prolog.$__32__372=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__373]);}),[]);
$Prolog.$__32__370=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__372,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__366=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__368,$Prolog.$__32__370]);}),[]);
$Prolog.$__32__363=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__365,$Prolog.$__32__366]);}),[]);
$Prolog.$__32__386=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["Y"]);}),[]);
$Prolog.$__32__385=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__386]);}),[]);
$Prolog.$__32__383=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__385,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__382=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["X"]);}),[]);
$Prolog.$__32__381=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__382]);}),[]);
$Prolog.$__32__379=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__381,$Prolog.$__32__383]);}),[]);
$Prolog.$__32__378=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["ouder"]);}),[]);
$Prolog.$__32__376=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__378,$Prolog.$__32__379]);}),[]);
$Prolog.$__32__374=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__376,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__361=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$_3a_3c_2d_3a,[$Prolog.$__32__363,$Prolog.$__32__374]);}),[]);
$Prolog.$__32__359=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__361,$Prolog.$__32__387]);}),[]);
$Prolog.$__32__354=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["Y"]);}),[]);
$Prolog.$__32__353=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__354]);}),[]);
$Prolog.$__32__358=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["X"]);}),[]);
$Prolog.$__32__357=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__358]);}),[]);
$Prolog.$__32__355=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__357,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__351=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__353,$Prolog.$__32__355]);}),[]);
$Prolog.$__32__350=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["ouder"]);}),[]);
$Prolog.$__32__348=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__350,$Prolog.$__32__351]);}),[]);
$Prolog.$__32__346=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__348,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__337=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["kind"]);}),[]);
$Prolog.$__32__345=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["Y"]);}),[]);
$Prolog.$__32__344=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__345]);}),[]);
$Prolog.$__32__342=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__344,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__341=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["X"]);}),[]);
$Prolog.$__32__340=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__341]);}),[]);
$Prolog.$__32__338=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__340,$Prolog.$__32__342]);}),[]);
$Prolog.$__32__335=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__337,$Prolog.$__32__338]);}),[]);
$Prolog.$__32__333=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$_3a_3c_2d_3a,[$Prolog.$__32__335,$Prolog.$__32__346]);}),[]);
$Prolog.$__32__331=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__333,$Prolog.$__32__359]);}),[]);
$Prolog.$__32__303=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__305,$Prolog.$__32__331]);}),[]);
$Prolog.$__32__294=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["pa"]);}),[]);
$Prolog.$__32__302=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["Y"]);}),[]);
$Prolog.$__32__301=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__302]);}),[]);
$Prolog.$__32__299=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__301,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__298=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["X"]);}),[]);
$Prolog.$__32__297=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__298]);}),[]);
$Prolog.$__32__295=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__297,$Prolog.$__32__299]);}),[]);
$Prolog.$__32__292=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__294,$Prolog.$__32__295]);}),[]);
$Prolog.$__32__290=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__292,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__289=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["Y"]);}),[]);
$Prolog.$__32__288=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__289]);}),[]);
$Prolog.$__32__286=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__288,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__285=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["X"]);}),[]);
$Prolog.$__32__284=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$Prolog.$__32__285]);}),[]);
$Prolog.$__32__282=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__284,$Prolog.$__32__286]);}),[]);
$Prolog.$__32__281=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["ouder"]);}),[]);
$Prolog.$__32__279=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Prolog.$__32__281,$Prolog.$__32__282]);}),[]);
$Prolog.$__32__277=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$_3a_3c_2d_3a,[$Prolog.$__32__279,$Prolog.$__32__290]);}),[]);
$Prolog.$__32__275=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__277,$Prolog.$__32__303]);}),[]);
$Prolog.$__32__266=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__268,$Prolog.$__32__275]);}),[]);
$Prolog.$__32__265=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["bea"]);}),[]);
$Prolog.$__32__263=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__265,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__262=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["juul"]);}),[]);
$Prolog.$__32__260=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__262,$Prolog.$__32__263]);}),[]);
$Prolog.$__32__259=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$maFact,[$Prolog.$__32__260]);}),[]);
$Prolog.$__32__257=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__259,$Prolog.$__32__266]);}),[]);
$Prolog.$__32__256=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["friso"]);}),[]);
$Prolog.$__32__254=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__256,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__253=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["bea"]);}),[]);
$Prolog.$__32__251=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__253,$Prolog.$__32__254]);}),[]);
$Prolog.$__32__250=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$maFact,[$Prolog.$__32__251]);}),[]);
$Prolog.$__32__248=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__250,$Prolog.$__32__257]);}),[]);
$Prolog.$__32__247=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["const"]);}),[]);
$Prolog.$__32__245=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__247,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__244=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["bea"]);}),[]);
$Prolog.$__32__242=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__244,$Prolog.$__32__245]);}),[]);
$Prolog.$__32__241=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$maFact,[$Prolog.$__32__242]);}),[]);
$Prolog.$__32__239=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__241,$Prolog.$__32__248]);}),[]);
$Prolog.$__32__238=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["alex"]);}),[]);
$Prolog.$__32__236=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__238,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__235=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["bea"]);}),[]);
$Prolog.$__32__233=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__235,$Prolog.$__32__236]);}),[]);
$Prolog.$__32__232=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$maFact,[$Prolog.$__32__233]);}),[]);
$Prolog.$__32__230=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__232,$Prolog.$__32__239]);}),[]);
$Prolog.$__32__221=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__223,$Prolog.$__32__230]);}),[]);
$Prolog.$__32__217=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["max"]);}),[]);
$Prolog.$__32__220=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["ale"]);}),[]);
$Prolog.$__32__218=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__220,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__215=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__217,$Prolog.$__32__218]);}),[]);
$Prolog.$__32__214=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$maFact,[$Prolog.$__32__215]);}),[]);
$Prolog.$__32__212=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__214,$Prolog.$__32__221]);}),[]);
$Prolog.$__32__146=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["ma"]);}),[]);
$Prolog.$__32__145=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$fact,[$Prolog.$__32__146]);}),[]);
$Prolog.$__32__147=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$map,[$Prolog.$cnst]);}),[]);
$Prolog.$maFact=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_2e,[$Prolog.$__32__145,$Prolog.$__32__147]);}),[]);
$Prolog.$__32__211=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["ama"]);}),[]);
$Prolog.$__32__209=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__211,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__208=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["max"]);}),[]);
$Prolog.$__32__206=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__208,$Prolog.$__32__209]);}),[]);
$Prolog.$__32__205=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$maFact,[$Prolog.$__32__206]);}),[]);
$Prolog.$__32__203=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__205,$Prolog.$__32__212]);}),[]);
$Prolog.$__32__194=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__196,$Prolog.$__32__203]);}),[]);
$Prolog.$__32__185=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__187,$Prolog.$__32__194]);}),[]);
$Prolog.$__32__176=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__178,$Prolog.$__32__185]);}),[]);
$Prolog.$__32__167=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__169,$Prolog.$__32__176]);}),[]);
$Prolog.$__32__166=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["ale"]);}),[]);
$Prolog.$__32__164=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__166,$UHC.$Base.$_5b_5d]);}),[]);
$Prolog.$__32__163=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["alex"]);}),[]);
$Prolog.$__32__161=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__163,$Prolog.$__32__164]);}),[]);
$Prolog.$__32__140=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["pa"]);}),[]);
$Prolog.$fact=
 new _F_(function($fn,$ts)
         {var $__=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$fn,$ts]);
          return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$_3a_3c_2d_3a,[$__,$UHC.$Base.$_5b_5d]);});
$Prolog.$__32__139=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$fact,[$Prolog.$__32__140]);}),[]);
$Prolog.$cnst=
 new _F_(function($s)
         {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$s,$UHC.$Base.$_5b_5d]);});
$Prolog.$__32__141=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$map,[$Prolog.$cnst]);}),[]);
$Prolog.$paFact=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_2e,[$Prolog.$__32__139,$Prolog.$__32__141]);}),[]);
$Prolog.$__32__160=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$paFact,[$Prolog.$__32__161]);}),[]);
$Prolog.$__32__158=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__160,$Prolog.$__32__167]);}),[]);
$Prolog.$exampleData=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Prolog.$__32__151,$Prolog.$__32__158]);}),[]);
$JCU.$loadExampleData=
 new _F_(function($__)
         {var $__2=
           new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0,$UHC.$Base.$False__]);
          var $__3=
           new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$JCU.$setRulesList,$__2]);
          var $__4=
           new _A_($JCU.$writeRulesInStore,[$Prolog.$exampleData]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__4,$__3]);});
$JCU.$__44__87NEW36=
 new _F_(function($_24x,$_24x2)
         {var $__=
           new _A_($Models.$tryParseRule,[$_24x2]);
          var $__4=
           new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0,[]]);
          var $__5=
           _e_($__);
          var $__swJSW39__0;
          switch($__5._tag_)
           {case 0:
             $__swJSW39__0=
              $__4;
             break;
            case 1:
             var $__7=
              new _A_($JCU.$markInvalidTerm,[$_24x]);
             $__swJSW39__0=
              $__7;
             break;}
          return $__swJSW39__0;});
$JCU.$_24okUNQ129=
 new _F_(function($_24x,$_24x2)
         {var $__=
           new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0,$UHC.$Base.$True__]);
          var $__4=
           new _A_($JCU.$__44__87NEW36,[$_24x,$_24x2]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__4,$__]);});
$JCU.$_24okUNQ121=
 new _F_(function($_24x)
         {var $__=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$valString,[$_24x]);
          var $__3=
           new _A_($JCU.$_24okUNQ129,[$_24x]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__,$__3]);});
$JCU.$checkTermSyntax=
 new _F_(function($__)
         {var $__2=
           new _A_($UHC.$Base.$packedStringToString,["#txtAddRule"]);
          var $__3=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$jQuery,[$__2]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__3,$JCU.$_24okUNQ121]);});
$JCU.$__44__631NEW293=
 new _F_(function($_24x)
         {var $__=
           new _A_($Models.$tryParseTerm,[$_24x]);
          var $__3=
           _e_($__);
          var $__swJSW40__0;
          switch($__3._tag_)
           {case 0:
             var $__5=
              new _A_($Data.$Tree.$Node__,[$__3._1,$UHC.$Base.$_5b_5d]);
             var $__6=
              new _A_($UHC.$Base.$_24,[$JCU.$replaceRuleTree,$__5]);
             $__swJSW40__0=
              $__6;
             break;
            case 1:
             var $__7=
              new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0,[]]);
             $__swJSW40__0=
              $__7;
             break;}
          return $__swJSW40__0;});
$JCU.$_24okUNQ479=
 new _F_(function($_24x)
         {var $__=
           new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0,$UHC.$Base.$False__]);
          var $__3=
           new _A_($JCU.$__44__631NEW293,[$_24x]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__3,$__]);});
$JCU.$startExampleGoal=
 new _F_(function($__)
         {var $__2=
           new _A_($UHC.$Base.$packedStringToString,["#startTerm"]);
          var $__3=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$jQuery,[$__2]);
          var $__4=
           new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__3,$Language.$UHC.$JS.$JQuery.$JQuery.$valString]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__4,$JCU.$_24okUNQ479]);});
$Language.$UHC.$JS.$JQuery.$JQuery.$KeyPress__=
 new _A_(new _F_(function()
                 {return {_tag_:9};}),[]);
$Control.$Monad.$when=
 new _F_(function($__,$p,$s)
         {var $__4=
           _e_($p);
          var $__swJSW41__0;
          switch($__4._tag_)
           {case 0:
             var $__5=
              new _A_($UHC.$Base.$return,[$__,[]]);
             $__swJSW41__0=
              $__5;
             break;
            case 1:
             $__swJSW41__0=
              $s;
             break;}
          return $__swJSW41__0;});
$Util.$void=
 new _F_(function($io)
         {var $__=
           new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0,[]]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$io,$__]);});
$JCU.$_24okUNQ681=
 new _F_(function($_24x)
         {var $__=
           new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0,$UHC.$Base.$True__]);
          var $__3=
           new _A_($UHC.$Base.$packedStringToString,["#txtAddRule"]);
          var $__4=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$jQuery,[$__3]);
          var $__5=
           new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__4,$JCU.$clearClasses]);
          var $__6=
           new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__5,$__]);
          var $__7=
           new _A_($JCU.$addRuleEvent,[$UHC.$Base.$undefined]);
          var $__8=
           new _A_($Util.$void,[$__7]);
          var $__9=
           new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__88__0,$_24x,13]);
          var $__10=
           new _A_($Control.$Monad.$when,[$UHC.$Base.$Monad__DCT74__339__0,$__9]);
          var $__11=
           new _A_($UHC.$Base.$_24,[$__10,$__8]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__11,$__6]);});
$JCU.$clrUNQ657=
 new _F_(function($obj)
         {var $__=
           new _A_($UHC.$Base.$packedStringToString,["which"]);
          var $__3=
           new _A_($Language.$UHC.$JS.$Primitives.$getAttr,[$__,$obj]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__3,$JCU.$_24okUNQ681]);});
$Language.$UHC.$JS.$JQuery.$JQuery.$__setValString=
 new _F_(function($__,$__2,$__3)
         {var $__4=
           _e_($__);
          var $__5=
           _e_($__2);
          var $__6=
           _e_($__4.val($__5));
          var $__7=
           _e_([]);
          return [$__3,$__7];});
$Language.$UHC.$JS.$JQuery.$JQuery.$setValString=
 new _F_(function($jq)
         {var $__=
           new _A_($Language.$UHC.$JS.$Types.$toJS,[$Language.$UHC.$JS.$ECMA.$String.$ToJS__DCT40__2__0]);
          var $__3=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$__setValString,[$jq]);
          return new _A_($UHC.$Base.$_2e,[$__3,$__]);});
$JCU.$modifyRulesInStore=
 new _F_(function($f)
         {var $__=
           new _A_($UHC.$Base.$fmap,[$UHC.$Base.$Functor__DCT74__338__0,$f,$JCU.$readRulesFromStore]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__,$JCU.$writeRulesInStore]);});
$UHC.$Base.$nNEW5959UNQ7297CCN=
 new _F_(function($x1,$x2)
         {var $x23=
           _e_($x2);
          var $__swJSW42__0;
          switch($x23._tag_)
           {case 0:
             var $__=
              new _A_($UHC.$Base.$_2d,[$UHC.$Base.$Num__DCT74__101__0,$x1,1]);
             var $__7=
              new _A_($UHC.$Base.$splitAt,[$__,$x23._2]);
             var $xs_27=
              new _A_($UHC.$Base.$xs_27NEW5965UNQ7307,[$__7]);
             var $xs_27_27=
              new _A_($UHC.$Base.$xs_27_27NEW5968UNQ7308,[$__7]);
             var $__10=
              new _A_($UHC.$Base.$_3a,[$x23._1,$xs_27]);
             $__swJSW42__0=
              [$__10,$xs_27_27];
             break;
            case 1:
             var $__=
              [$UHC.$Base.$_5b_5d,$UHC.$Base.$_5b_5d];
             $__swJSW42__0=
              $__;
             break;}
          return $__swJSW42__0;});
$UHC.$Base.$xs_27NEW5965UNQ7307=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return $__2[0];});
$UHC.$Base.$xs_27_27NEW5968UNQ7308=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return $__2[1];});
$UHC.$Base.$splitAt=
 new _F_(function($x1,$x2)
         {var $n=
           new _A_($UHC.$Base.$nNEW5959UNQ7297CCN,[$x1,$x2]);
          var $__=
           new _A_($UHC.$Base.$_3c_3d,[$UHC.$Base.$Ord__DCT74__91__0,$x1,0]);
          var $__5=
           _e_($__);
          var $__swJSW45__0;
          switch($__5._tag_)
           {case 0:
             $__swJSW45__0=
              $n;
             break;
            case 1:
             var $__6=
              [$UHC.$Base.$_5b_5d,$x2];
             $__swJSW45__0=
              $__6;
             break;}
          return $__swJSW45__0;});
$JCU.$ysNEW356UNQ510=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return $__2[0];});
$JCU.$zsNEW359UNQ511=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return $__2[1];});
$UHC.$Base.$tail=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          var $__swJSW48__0;
          switch($__2._tag_)
           {case 0:
             $__swJSW48__0=
              $__2._2;
             break;
            case 1:
             $__swJSW48__0=
              $UHC.$Base.$undefined;
             break;}
          return $__swJSW48__0;});
$JCU.$dropXUNQ505=
 new _F_(function($id,$rules)
         {var $__=
           new _A_($UHC.$Base.$splitAt,[$id,$rules]);
          var $ys=
           new _A_($JCU.$ysNEW356UNQ510,[$__]);
          var $zs=
           new _A_($JCU.$zsNEW359UNQ511,[$__]);
          var $__6=
           new _A_($UHC.$Base.$tail,[$zs]);
          return new _A_($UHC.$Base.$_2b_2b,[$ys,$__6]);});
$JCU.$deleteRuleFromStore=
 new _F_(function($id)
         {var $__=
           new _A_($JCU.$dropXUNQ505,[$id]);
          return new _A_($JCU.$modifyRulesInStore,[$__]);});
$Language.$UHC.$JS.$JQuery.$Draggable.$__draggable=
 new _F_(function($__,$__2,$__3)
         {var $__4=
           _e_($__);
          var $__5=
           _e_($__2);
          var $__6=
           _e_($__4.draggable($__5));
          var $__7=
           _e_([]);
          return [$__3,$__7];});
$Language.$UHC.$JS.$JQuery.$Draggable.$_24okUNQ210=
 new _F_(function($jq,$_24x)
         {return new _A_($Language.$UHC.$JS.$JQuery.$Draggable.$__draggable,[$jq,$_24x]);});
$Language.$UHC.$JS.$JQuery.$Draggable.$mkJSDraggable=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_(primToPlainObj($__3));
          return [$__2,$__4];});
$Language.$UHC.$JS.$JQuery.$Draggable.$draggable=
 new _F_(function($jq,$drag)
         {var $__=
           new _A_($Language.$UHC.$JS.$JQuery.$Draggable.$mkJSDraggable,[$drag]);
          var $__4=
           new _A_($Language.$UHC.$JS.$JQuery.$Draggable.$_24okUNQ210,[$jq]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__,$__4]);});
$Language.$UHC.$JS.$JQuery.$JQuery.$__click=
 new _F_(function($__,$__2,$__3)
         {var $__4=
           _e_($__);
          var $__5=
           _e_($__2);
          var $__6=
           _e_($__4.click($__5));
          var $__7=
           _e_([]);
          return [$__3,$__7];});
$Language.$UHC.$JS.$JQuery.$JQuery.$click=
 new _F_(function($jq,$eh)
         {var $__=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$__click,[$jq]);
          var $__4=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$mkJEventHandler,[$eh]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__4,$__]);});
$Language.$UHC.$JS.$JQuery.$Draggable.$Draggable__=
 new _F_(function($x1,$x2,$x3,$x4,$x5,$x6)
         {return {_tag_:0,scroll:$x1,containment:$x2,revert:$x3,revertDuration:$x4,scrollSensitivity:$x5,start:$x6};});
$Language.$UHC.$JS.$JQuery.$JQuery.$mkJUIEventHandler=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_(function(v1,v2)
               {var res=
                 _e_(new _A_($__3,[v1,v2,[]]));
                _e_(res[0]);
                return _e_(res[1]);});
          return [$__2,$__4];});
$Language.$UHC.$JS.$JQuery.$JQuery.$doBlur=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__3.blur());
          var $__5=
           _e_([]);
          return [$__2,$__5];});
$Language.$UHC.$JS.$ECMA.$Bool.$__true=
 new _A_(new _F_(function()
                 {return true;}),[]);
$Language.$UHC.$JS.$ECMA.$Bool.$__false=
 new _A_(new _F_(function()
                 {return false;}),[]);
$Language.$UHC.$JS.$ECMA.$Bool.$toJSBool=
 new _F_(function($x1)
         {var $__=
           _e_($x1);
          var $__swJSW49__0;
          switch($__._tag_)
           {case 0:
             $__swJSW49__0=
              $Language.$UHC.$JS.$ECMA.$Bool.$__false;
             break;
            case 1:
             $__swJSW49__0=
              $Language.$UHC.$JS.$ECMA.$Bool.$__true;
             break;}
          return $__swJSW49__0;});
$Language.$UHC.$JS.$ECMA.$Bool.$ToJS__NEW25UNQ27EVLDCT64__0__0RDC=
 new _F_(function($ToJS__)
         {var $ToJS__2=
           _e_(new _A_($Language.$UHC.$JS.$Types.$ToJS__CLS28__3__0,[$ToJS__]));
          var $__4=
           {_tag_:0,_1:$Language.$UHC.$JS.$ECMA.$Bool.$toJSBool};
          return $__4;});
$Language.$UHC.$JS.$ECMA.$Bool.$ToJS__NEW23UNQ26DCT64__0__0RDC=
 new _F_(function($ToJS__)
         {var $ToJS__2=
           new _A_($Language.$UHC.$JS.$ECMA.$Bool.$ToJS__NEW25UNQ27EVLDCT64__0__0RDC,[$ToJS__]);
          return $ToJS__2;});
$Language.$UHC.$JS.$ECMA.$Bool.$ToJS__UNQ26DCT64__0__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($Language.$UHC.$JS.$ECMA.$Bool.$ToJS__NEW23UNQ26DCT64__0__0RDC,[$Language.$UHC.$JS.$ECMA.$Bool.$ToJS__UNQ26DCT64__0__0RDC]);}),[]);
$Language.$UHC.$JS.$ECMA.$Bool.$ToJS__DCT64__0__0=
 new _A_(new _F_(function()
                 {return $Language.$UHC.$JS.$ECMA.$Bool.$ToJS__UNQ26DCT64__0__0RDC;}),[]);
$Templates.$rules__list__item=
 new _F_(function($rule)
         {var $__=
           new _A_($UHC.$Base.$packedStringToString,["</span>  <span class=\"buttons\"><button class=\"btnDeleteList\" type=\"button\" value=\"X\" /></span</div>"]);
          var $__3=
           new _A_($UHC.$Base.$_2b_2b,[$rule,$__]);
          var $__4=
           new _A_($UHC.$Base.$packedStringToString,["\" class=\"draggable rule-list-item ui-widget-content\">  <span class=\"rule-text\">"]);
          var $__5=
           new _A_($UHC.$Base.$_2b_2b,[$__4,$__3]);
          var $__6=
           new _A_($UHC.$Base.$_2b_2b,[$rule,$__5]);
          var $__7=
           new _A_($UHC.$Base.$packedStringToString,["<div id=\"rule_"]);
          return new _A_($UHC.$Base.$_2b_2b,[$__7,$__6]);});
$JCU.$_24okUNQ594=
 new _F_(function($id,$_24x)
         {var $__=
           new _A_($UHC.$Base.$packedStringToString,["button.btnDeleteList"]);
          var $__4=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$findSelector,[$_24x,$__]);
          var $__5=
           new _A_($JCU.$_24okUNQ601,[$id,$_24x]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__4,$__5]);});
$JCU.$_24okUNQ601=
 new _F_(function($id,$_24x,$_24x3)
         {var $__=
           new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0,$_24x]);
          var $__5=
           new _A_($JCU.$deleteRule,[$_24x,$id]);
          var $__6=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$click,[$_24x3,$__5]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__6,$__]);});
$JCU.$_24okUNQ526=
 new _F_(function($_24x)
         {var $__=
           new _A_($JCU.$__44__831NEW369,[$_24x]);
          var $__3=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$empty,[$_24x]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__3,$__]);});
$JCU.$__44__831NEW369=
 new _F_(function($_24x)
         {var $__=
           new _A_($JCU.$_24okUNQ537,[$_24x]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$JCU.$readRulesFromStore,$__]);});
$JCU.$_24okUNQ537=
 new _F_(function($_24x,$_24x2)
         {var $__=
           new _A_($UHC.$Base.$enumFrom,[$UHC.$Base.$Enum__DCT74__118__0,0]);
          var $__4=
           new _A_($UHC.$Base.$zip,[$__,$_24x2]);
          var $__5=
           new _A_($JCU.$fUNQ542,[$_24x,$Language.$Prolog.$NanoProlog.$NanoProlog.$Show__DCT52__15__0]);
          var $__6=
           new _A_($UHC.$Base.$mapM__,[$UHC.$Base.$Monad__DCT74__339__0,$__5,$__4]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__6,$JCU.$__44__869]);});
$JCU.$fUNQ542=
 new _F_(function($_24x,$__,$__3)
         {var $__4=
           _e_($__3);
          var $__7=
           new _A_($UHC.$Base.$show,[$__,$__4[1]]);
          var $__8=
           new _A_($JCU.$createRuleLi,[$__7,$__4[0]]);
          var $__9=
           new _A_($JCU.$_24okUNQ559,[$_24x]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__8,$__9]);});
$JCU.$_24okUNQ559=
 new _F_(function($_24x,$_24x2)
         {var $__=
           new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0,[]]);
          var $__4=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$append,[$_24x,$_24x2]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__4,$__]);});
$JCU.$__44__869=
 new _A_(new _F_(function()
                 {var $__=
                   new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$mkJUIEventHandler,[$JCU.$__44__905__0]);
                  return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__,$JCU.$_24okUNQ565]);}),[]);
$JCU.$_24okUNQ565=
 new _F_(function($_24x)
         {var $__=
           new _A_($UHC.$Base.$packedStringToString,[".draggable"]);
          var $__3=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$jQuery,[$__]);
          var $__4=
           new _A_($JCU.$_24okUNQ577,[$_24x]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__3,$__4]);});
$JCU.$_24okUNQ577=
 new _F_(function($_24x,$_24x2)
         {var $__=
           new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0,[]]);
          var $__4=
           new _A_($Language.$UHC.$JS.$Types.$toJS,[$Language.$UHC.$JS.$ECMA.$Bool.$ToJS__DCT64__0__0,$UHC.$Base.$True__]);
          var $__5=
           new _A_($UHC.$Base.$packedStringToString,["document"]);
          var $__6=
           new _A_($Language.$UHC.$JS.$Types.$toJS,[$Language.$UHC.$JS.$ECMA.$String.$ToJS__DCT40__2__0,$__5]);
          var $__7=
           new _A_($Language.$UHC.$JS.$Types.$toJS,[$Language.$UHC.$JS.$ECMA.$Bool.$ToJS__DCT64__0__0,$UHC.$Base.$True__]);
          var $__8=
           new _A_($Language.$UHC.$JS.$JQuery.$Draggable.$Draggable__,[$__7,$__6,$__4,100,50,$_24x]);
          var $__9=
           new _A_($Language.$UHC.$JS.$JQuery.$Draggable.$draggable,[$_24x2]);
          var $__10=
           new _A_($UHC.$Base.$_24,[$__9,$__8]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__10,$__]);});
$JCU.$__44__905__0=
 new _F_(function($x,$y)
         {var $__=
           new _A_($UHC.$Base.$packedStringToString,[":focus"]);
          var $__4=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$jQuery,[$__]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__4,$JCU.$_24okUNQ586]);});
$JCU.$_24okUNQ586=
 new _F_(function($_24x)
         {var $__=
           new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0,$UHC.$Base.$False__]);
          var $__3=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$doBlur,[$_24x]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__3,$__]);});
$JCU.$setRulesList=
 new _A_(new _F_(function()
                 {var $__=
                   new _A_($UHC.$Base.$packedStringToString,["#rules-list-view"]);
                  var $__2=
                   new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$jQuery,[$__]);
                  return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__2,$JCU.$_24okUNQ526]);}),[]);
$JCU.$createRuleLi=
 new _F_(function($rule,$id)
         {var $__=
           new _A_($UHC.$Base.$packedStringToString,["</li>"]);
          var $__4=
           new _A_($Templates.$rules__list__item,[$rule]);
          var $__5=
           new _A_($UHC.$Base.$_2b_2b,[$__4,$__]);
          var $__6=
           new _A_($UHC.$Base.$packedStringToString,["<li>"]);
          var $__7=
           new _A_($UHC.$Base.$_2b_2b,[$__6,$__5]);
          var $__8=
           new _A_($UHC.$Base.$_24,[$Language.$UHC.$JS.$JQuery.$JQuery.$jQuery,$__7]);
          var $__9=
           new _A_($JCU.$_24okUNQ594,[$id]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__8,$__9]);});
$JCU.$deleteRule=
 new _F_(function($jq,$i,$__)
         {var $__4=
           new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0,$UHC.$Base.$False__]);
          var $__5=
           new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$JCU.$setRulesList,$__4]);
          var $__6=
           new _A_($JCU.$deleteRuleFromStore,[$i]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__6,$__5]);});
$JCU.$_24okUNQ633=
 new _F_(function($_24x)
         {var $__=
           new _A_($UHC.$Base.$packedStringToString,[""]);
          var $__3=
           new _A_($UHC.$Base.$flip,[$Language.$UHC.$JS.$JQuery.$JQuery.$setValString,$__]);
          var $__4=
           new _A_($UHC.$Base.$packedStringToString,["#txtAddRule"]);
          var $__5=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$jQuery,[$__4]);
          var $__6=
           new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__5,$__3]);
          var $__7=
           new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$JCU.$setRulesList,$__6]);
          var $__8=
           _e_($_24x);
          var $__swJSW52__0;
          switch($__8._tag_)
           {case 0:
             $__swJSW52__0=
              $__7;
             break;
            case 1:
             var $__10=
              new _A_($UHC.$Base.$packedStringToString,["Rule already exists"]);
             var $__11=
              new _A_($Util.$showError,[$__10]);
             $__swJSW52__0=
              $__11;
             break;}
          return $__swJSW52__0;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$__Rep0RuleDFLUHC_2eBase_2efrom0GENRepresentable0=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          var $__5=
           new _A_($UHC.$Base.$K1__,[$x2._2]);
          var $__6=
           new _A_($UHC.$Base.$M1__,[$__5]);
          var $__7=
           new _A_($UHC.$Base.$K1__,[$x2._1]);
          var $__8=
           new _A_($UHC.$Base.$M1__,[$__7]);
          var $__9=
           new _A_($UHC.$Base.$_3a_2a_3a,[$__8,$__6]);
          var $__10=
           new _A_($UHC.$Base.$M1__,[$__9]);
          var $__11=
           new _A_($UHC.$Base.$M1__,[$__10]);
          return $__11;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$__Rep0RuleDFLUHC_2eBase_2eto0GENRepresentable0=
 new _F_(function($proj__1)
         {var $proj__3=
           _e_($proj__1);
          var $__=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$_3a_3c_2d_3a,[$proj__3._1,$proj__3._2]);
          return $__;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$__Rep0RuleNEW448UNQ157EVLSDCGENRepresentable0=
 new _F_(function($__)
         {var $Representable0__=
           _e_(new _A_($UHC.$Base.$Representable0__CLS74__369__0,[$__]));
          var $__5=
           {_tag_:0,_1:$Language.$Prolog.$NanoProlog.$NanoProlog.$__Rep0RuleDFLUHC_2eBase_2efrom0GENRepresentable0,_2:$Language.$Prolog.$NanoProlog.$NanoProlog.$__Rep0RuleDFLUHC_2eBase_2eto0GENRepresentable0};
          return $__5;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$__Rep0RuleNEW446UNQ156SDCGENRepresentable0=
 new _F_(function($__)
         {var $__2=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$__Rep0RuleNEW448UNQ157EVLSDCGENRepresentable0,[$__]);
          return $__2;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$__Rep0RuleUNQ156SDCGENRepresentable0=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$__Rep0RuleNEW446UNQ156SDCGENRepresentable0,[$Language.$Prolog.$NanoProlog.$NanoProlog.$__Rep0RuleUNQ156SDCGENRepresentable0]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__Rep0RuleGENRepresentable0=
 new _A_(new _F_(function()
                 {return $Language.$Prolog.$NanoProlog.$NanoProlog.$__Rep0RuleUNQ156SDCGENRepresentable0;}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__4498__2__9UNQ946=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Eq__DCT74__394__0,[$Language.$Prolog.$NanoProlog.$NanoProlog.$__52__0__0]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__4498__2__8UNQ945=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Eq_27__DCT74__390__0,[$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__4498__2__9UNQ946]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__4498__2__7UNQ944=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Eq_27__DCT74__391__0,[$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__4498__2__8UNQ945]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__Rep0TermDFLUHC_2eBase_2efrom0GENRepresentable0=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          var $__swJSW56__0;
          switch($x2._tag_)
           {case 0:
             var $__5=
              new _A_($UHC.$Base.$K1__,[$x2._2]);
             var $__6=
              new _A_($UHC.$Base.$M1__,[$__5]);
             var $__7=
              new _A_($UHC.$Base.$K1__,[$x2._1]);
             var $__8=
              new _A_($UHC.$Base.$M1__,[$__7]);
             var $__9=
              new _A_($UHC.$Base.$_3a_2a_3a,[$__8,$__6]);
             var $__10=
              new _A_($UHC.$Base.$M1__,[$__9]);
             var $__11=
              new _A_($UHC.$Base.$R1__,[$__10]);
             var $__12=
              new _A_($UHC.$Base.$M1__,[$__11]);
             $__swJSW56__0=
              $__12;
             break;
            case 1:
             var $__14=
              new _A_($UHC.$Base.$K1__,[$x2._1]);
             var $__15=
              new _A_($UHC.$Base.$M1__,[$__14]);
             var $__16=
              new _A_($UHC.$Base.$M1__,[$__15]);
             var $__17=
              new _A_($UHC.$Base.$L1__,[$__16]);
             var $__18=
              new _A_($UHC.$Base.$M1__,[$__17]);
             $__swJSW56__0=
              $__18;
             break;}
          return $__swJSW56__0;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$__Rep0TermDFLUHC_2eBase_2eto0GENRepresentable0=
 new _F_(function($proj__1)
         {var $proj__2=
           _e_($proj__1);
          var $__swJSW57__0;
          switch($proj__2._tag_)
           {case 0:
             var $__=
              new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$proj__2.unL1]);
             $__swJSW57__0=
              $__;
             break;
            case 1:
             var $proj__7=
              _e_($proj__2.unR1);
             var $__=
              new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$proj__7._1,$proj__7._2]);
             $__swJSW57__0=
              $__;
             break;}
          return $__swJSW57__0;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$__Rep0TermNEW348UNQ59EVLSDCGENRepresentable0=
 new _F_(function($__)
         {var $Representable0__=
           _e_(new _A_($UHC.$Base.$Representable0__CLS74__369__0,[$__]));
          var $__5=
           {_tag_:0,_1:$Language.$Prolog.$NanoProlog.$NanoProlog.$__Rep0TermDFLUHC_2eBase_2efrom0GENRepresentable0,_2:$Language.$Prolog.$NanoProlog.$NanoProlog.$__Rep0TermDFLUHC_2eBase_2eto0GENRepresentable0};
          return $__5;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$__Rep0TermNEW346UNQ58SDCGENRepresentable0=
 new _F_(function($__)
         {var $__2=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$__Rep0TermNEW348UNQ59EVLSDCGENRepresentable0,[$__]);
          return $__2;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$__Rep0TermUNQ58SDCGENRepresentable0=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$__Rep0TermNEW346UNQ58SDCGENRepresentable0,[$Language.$Prolog.$NanoProlog.$NanoProlog.$__Rep0TermUNQ58SDCGENRepresentable0]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__Rep0TermGENRepresentable0=
 new _A_(new _F_(function()
                 {return $Language.$Prolog.$NanoProlog.$NanoProlog.$__Rep0TermUNQ58SDCGENRepresentable0;}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3626__2__3UNQ801=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Eq_27__DCT74__391__0,[$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3626__2__4UNQ803]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3626__2__6UNQ795=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Eq__DCT74__394__0,[$UHC.$Base.$Eq__DCT74__56__0]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3626__2__5UNQ794=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Eq_27__DCT74__390__0,[$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3626__2__6UNQ795]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3626__2__4UNQ803=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Eq_27__DCT74__391__0,[$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3626__2__5UNQ794]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__52__0__0NEW372UNQ804EVLRDC=
 new _F_(function($__,$__2)
         {var $Eq__=
           _e_(new _A_($UHC.$Base.$Eq__CLS74__4__0,[$__]));
          var $__6=
           {_tag_:0,_1:$Eq__._1,_2:$__2};
          return $__6;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$__52__0__0NEW360UNQ786RDC=
 new _F_(function($__,$__2,$__3,$__4,$__5,$__6,$__7,$__8,$__9,$__10,$__11)
         {var $__12=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$__52__0__0NEW372UNQ804EVLRDC,[$__10,$__11]);
          return $__12;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3626__2__14UNQ790=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Eq_27__DCT74__391__0,[$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3626__2__15UNQ789]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3626__2__15UNQ789=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Eq_27__DCT74__390__0,[$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3626__2__16UNQ788]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3626__2__16UNQ788=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Eq__DCT74__394__0,[$Language.$Prolog.$NanoProlog.$NanoProlog.$__52__0__0UNQ786RDC]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__52__0__0UNQ786RDC=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$__52__0__0NEW360UNQ786RDC,[$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3626__2__14UNQ790,$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3626__2__15UNQ789,$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3626__2__16UNQ788,$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3626__2__9UNQ791,$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3626__2__8UNQ792,$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3626__2__4UNQ803,$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3626__2__3UNQ801,$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3626__2__2UNQ787,$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3634__0__4__0UNQ793,$Language.$Prolog.$NanoProlog.$NanoProlog.$__52__0__0UNQ786RDC,$Language.$Prolog.$NanoProlog.$NanoProlog.$__52__0__0DFLUHC_2eBase_2e_3d_3d]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3626__2__9UNQ791=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Eq_27__DCT74__393__0,[$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3626__2__4UNQ803,$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3626__2__14UNQ790]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3626__2__8UNQ792=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Eq_27__DCT74__391__0,[$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3626__2__9UNQ791]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3626__2__2UNQ787=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Eq_27__DCT74__392__0,[$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3626__2__3UNQ801,$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3626__2__8UNQ792]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3634__0__4__0UNQ793=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Eq_27__DCT74__391__0,[$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3626__2__2UNQ787]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__52__0__0DFLUHC_2eBase_2e_3d_3d=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$geqdefault,[$Language.$Prolog.$NanoProlog.$NanoProlog.$__Rep0TermGENRepresentable0,$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__3634__0__4__0UNQ793,$UHC.$Base.$undefined]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__52__0__0=
 new _A_(new _F_(function()
                 {return $Language.$Prolog.$NanoProlog.$NanoProlog.$__52__0__0UNQ786RDC;}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__4498__2__5UNQ941=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Eq_27__DCT74__390__0,[$Language.$Prolog.$NanoProlog.$NanoProlog.$__52__0__0]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__4498__2__4UNQ951=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Eq_27__DCT74__391__0,[$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__4498__2__5UNQ941]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__4498__2__3UNQ949=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Eq_27__DCT74__393__0,[$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__4498__2__4UNQ951,$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__4498__2__7UNQ944]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__4498__2__2UNQ948=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Eq_27__DCT74__391__0,[$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__4498__2__3UNQ949]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__4506__0__4__0UNQ943=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Eq_27__DCT74__391__0,[$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__4498__2__2UNQ948]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__52__2__0DFLUHC_2eBase_2e_3d_3d=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$geqdefault,[$Language.$Prolog.$NanoProlog.$NanoProlog.$__Rep0RuleGENRepresentable0,$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__4506__0__4__0UNQ943,$UHC.$Base.$undefined]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__52__2__0NEW465UNQ952EVLRDC=
 new _F_(function($__,$__2)
         {var $Eq__=
           _e_(new _A_($UHC.$Base.$Eq__CLS74__4__0,[$__]));
          var $__6=
           {_tag_:0,_1:$Eq__._1,_2:$__2};
          return $__6;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$__52__2__0NEW462UNQ940RDC=
 new _F_(function($__,$__2)
         {var $__3=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$__52__2__0NEW465UNQ952EVLRDC,[$__,$__2]);
          return $__3;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$__52__2__0UNQ940RDC=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$__52__2__0NEW462UNQ940RDC,[$Language.$Prolog.$NanoProlog.$NanoProlog.$__52__2__0UNQ940RDC,$Language.$Prolog.$NanoProlog.$NanoProlog.$__52__2__0DFLUHC_2eBase_2e_3d_3d]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__52__2__0=
 new _A_(new _F_(function()
                 {return $Language.$Prolog.$NanoProlog.$NanoProlog.$__52__2__0UNQ940RDC;}),[]);
$Data.$List.$_24okUNQ444=
 new _F_(function($p,$_24x)
         {var $__=
           _e_($_24x);
          var $__6=
           new _A_($p,[$__[0]]);
          var $__7=
           _e_($__6);
          var $__swJSW63__0;
          switch($__7._tag_)
           {case 0:
             $__swJSW63__0=
              $UHC.$Base.$_5b_5d;
             break;
            case 1:
             var $__8=
              new _A_($UHC.$Base.$_3a,[$__[1],$UHC.$Base.$_5b_5d]);
             $__swJSW63__0=
              $__8;
             break;}
          return $__swJSW63__0;});
$Data.$List.$findIndices=
 new _F_(function($p,$xs)
         {var $__=
           new _A_($UHC.$Base.$enumFrom,[$UHC.$Base.$Enum__DCT74__118__0,0]);
          var $__4=
           new _A_($UHC.$Base.$zip,[$xs,$__]);
          var $__5=
           new _A_($Data.$List.$_24okUNQ444,[$p]);
          return new _A_($UHC.$Base.$concatMap,[$__5,$__4]);});
$Data.$List.$findIndex=
 new _F_(function($p)
         {var $__=
           new _A_($Data.$List.$findIndices,[$p]);
          return new _A_($UHC.$Base.$_2e,[$Data.$Maybe.$listToMaybe,$__]);});
$Data.$List.$elemIndex=
 new _F_(function($__,$x)
         {var $__3=
           new _A_($UHC.$Base.$_3d_3d,[$__,$x]);
          return new _A_($Data.$List.$findIndex,[$__3]);});
$JCU.$__44__745=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["rules"]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$Show__DCT52__15__0DFLUHC_2eBase_2eshow=
 new _F_(function($x1)
         {var $__=
           _e_($x1);
          var $__5=
           new _A_($UHC.$Base.$packedStringToString,["."]);
          var $__6=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$showCommas,[$Language.$Prolog.$NanoProlog.$NanoProlog.$Show__DCT52__14__0,$__._2]);
          var $__7=
           new _A_($UHC.$Base.$_2b_2b,[$__6,$__5]);
          var $__8=
           new _A_($UHC.$Base.$packedStringToString,[":-"]);
          var $__9=
           new _A_($UHC.$Base.$_2b_2b,[$__8,$__7]);
          var $__10=
           new _A_($UHC.$Base.$show,[$Language.$Prolog.$NanoProlog.$NanoProlog.$Show__DCT52__14__0,$__._1]);
          var $__11=
           new _A_($UHC.$Base.$_2b_2b,[$__10,$__9]);
          var $__12=
           _e_($__._2);
          var $__swJSW65__0;
          switch($__12._tag_)
           {case 0:
             $__swJSW65__0=
              $__11;
             break;
            case 1:
             var $__15=
              new _A_($UHC.$Base.$packedStringToString,["."]);
             var $__16=
              new _A_($UHC.$Base.$show,[$Language.$Prolog.$NanoProlog.$NanoProlog.$Show__DCT52__14__0,$__._1]);
             var $__17=
              new _A_($UHC.$Base.$_2b_2b,[$__16,$__15]);
             $__swJSW65__0=
              $__17;
             break;}
          return $__swJSW65__0;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$Show__NEW285UNQ812EVLDCT52__15__0RDC=
 new _F_(function($Show__)
         {var $Show__2=
           _e_(new _A_($UHC.$Base.$Show__CLS74__43__0,[$Show__]));
          var $__6=
           {_tag_:0,_1:$Language.$Prolog.$NanoProlog.$NanoProlog.$Show__DCT52__15__0DFLUHC_2eBase_2eshow,_2:$Show__2._2,_3:$Show__2._3};
          return $__6;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$Show__NEW283UNQ808DCT52__15__0RDC=
 new _F_(function($Show__)
         {var $Show__2=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Show__NEW285UNQ812EVLDCT52__15__0RDC,[$Show__]);
          return $Show__2;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$Show__UNQ808DCT52__15__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Show__NEW283UNQ808DCT52__15__0RDC,[$Language.$Prolog.$NanoProlog.$NanoProlog.$Show__UNQ808DCT52__15__0RDC]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$Show__DCT52__15__0=
 new _A_(new _F_(function()
                 {return $Language.$Prolog.$NanoProlog.$NanoProlog.$Show__UNQ808DCT52__15__0RDC;}),[]);
$JCU.$__42__5320__2__0=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Show__DCT74__87__0,[$Language.$Prolog.$NanoProlog.$NanoProlog.$Show__DCT52__15__0]);}),[]);
$JCU.$writeRulesInStore=
 new _A_(new _F_(function()
                 {return new _A_($Data.$LocalStorage.$setLocalStorage,[$JCU.$__42__5320__2__0,$JCU.$__44__745]);}),[]);
$JCU.$_24okUNQ495=
 new _F_(function($rule,$_24x)
         {var $__=
           new _A_($Data.$List.$elemIndex,[$Language.$Prolog.$NanoProlog.$NanoProlog.$__52__2__0,$rule,$_24x]);
          var $__4=
           _e_($__);
          var $__swJSW67__0;
          switch($__4._tag_)
           {case 0:
             var $__6=
              new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0,$UHC.$Base.$Nothing__]);
             $__swJSW67__0=
              $__6;
             break;
            case 1:
             var $__7=
              new _A_($UHC.$Base.$length,[$_24x]);
             var $__8=
              new _A_($UHC.$Base.$_2b,[$UHC.$Base.$Num__DCT74__101__0,$__7,1]);
             var $__9=
              new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0]);
             var $__10=
              new _A_($UHC.$Base.$_2e,[$__9,$UHC.$Base.$Just__]);
             var $__11=
              new _A_($UHC.$Base.$_24,[$__10,$__8]);
             var $__12=
              new _A_($UHC.$Base.$_3a,[$rule,$UHC.$Base.$_5b_5d]);
             var $__13=
              new _A_($UHC.$Base.$_2b_2b,[$_24x,$__12]);
             var $__14=
              new _A_($JCU.$writeRulesInStore,[$__13]);
             var $__15=
              new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__14,$__11]);
             $__swJSW67__0=
              $__15;
             break;}
          return $__swJSW67__0;});
$JCU.$addRuleToStore=
 new _F_(function($rule)
         {var $__=
           new _A_($JCU.$_24okUNQ495,[$rule]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$JCU.$readRulesFromStore,$__]);});
$JCU.$__44__977NEW423=
 new _F_(function($_24x)
         {var $__=
           new _A_($Language.$UHC.$JS.$Types.$fromJS,[$Language.$UHC.$JS.$ECMA.$String.$FromJS__DCT40__4__0,$_24x]);
          var $__3=
           new _A_($Models.$tryParseRule,[$__]);
          var $__4=
           _e_($__3);
          var $__swJSW68__0;
          switch($__4._tag_)
           {case 0:
             var $__6=
              new _A_($JCU.$addRuleToStore,[$__4._1]);
             $__swJSW68__0=
              new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__6,$JCU.$_24okUNQ633]);
             break;
            case 1:
             var $__7=
              new _A_($Language.$UHC.$JS.$Types.$fromJS,[$Language.$UHC.$JS.$ECMA.$String.$FromJS__DCT40__4__0,$_24x]);
             var $__8=
              new _A_($UHC.$Base.$packedStringToString,["Invalid rule, not adding to rule list."]);
             var $__9=
              new _A_($UHC.$Base.$_2b_2b,[$__8,$__7]);
             var $__10=
              new _A_($UHC.$Base.$_24,[$Util.$showError,$__9]);
             $__swJSW68__0=
              $__10;
             break;}
          return $__swJSW68__0;});
$JCU.$_24okUNQ622=
 new _F_(function($_24x)
         {var $__=
           new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0,$UHC.$Base.$True__]);
          var $__3=
           new _A_($JCU.$__44__977NEW423,[$_24x]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__3,$__]);});
$JCU.$addRuleEvent=
 new _F_(function($event)
         {var $__=
           new _A_($UHC.$Base.$packedStringToString,["#txtAddRule"]);
          var $__3=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$jQuery,[$__]);
          var $__4=
           new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__3,$Language.$UHC.$JS.$JQuery.$JQuery.$valJSString]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__4,$JCU.$_24okUNQ622]);});
$JCU.$__44__1148NEW517=
 new _F_(function($_24x)
         {var $__=
           new _A_($UHC.$Base.$not,[$_24x]);
          var $__3=
           _e_($__);
          var $__swJSW69__0;
          switch($__3._tag_)
           {case 0:
             var $__4=
              new _A_($UHC.$Base.$packedStringToString,["noClue"]);
             var $__5=
              new _A_($UHC.$Base.$flip,[$Language.$UHC.$JS.$JQuery.$JQuery.$removeClass_27,$__4]);
             var $__6=
              new _A_($UHC.$Base.$packedStringToString,["#proof-tree-div"]);
             var $__7=
              new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$jQuery,[$__6]);
             var $__8=
              new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__7,$__5]);
             $__swJSW69__0=
              $__8;
             break;
            case 1:
             var $__9=
              new _A_($UHC.$Base.$packedStringToString,["noClue"]);
             var $__10=
              new _A_($UHC.$Base.$flip,[$Language.$UHC.$JS.$JQuery.$JQuery.$addClass,$__9]);
             var $__11=
              new _A_($UHC.$Base.$packedStringToString,["#proof-tree-div"]);
             var $__12=
              new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$jQuery,[$__11]);
             var $__13=
              new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__12,$__10]);
             $__swJSW69__0=
              $__13;
             break;}
          return $__swJSW69__0;});
$JCU.$resetTreeUNQ664=
 new _F_(function($__)
         {var $__2=
           new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0,$UHC.$Base.$True__]);
          var $__3=
           new _A_($JCU.$replaceRuleTree,[$JCU.$emptyProof]);
          var $__4=
           new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__3,$__2]);
          var $__5=
           new _A_($Data.$LocalStorage.$setLocalStorage,[$UHC.$Base.$__74__50__0,$JCU.$checkProofStoreKey,$UHC.$Base.$False__]);
          var $__6=
           new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__5,$__4]);
          var $__7=
           new _A_($UHC.$Base.$packedStringToString,["noClue"]);
          var $__8=
           new _A_($UHC.$Base.$flip,[$Language.$UHC.$JS.$JQuery.$JQuery.$addClass,$__7]);
          var $__9=
           new _A_($UHC.$Base.$packedStringToString,["#proof-tree-div"]);
          var $__10=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$jQuery,[$__9]);
          var $__11=
           new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__10,$__8]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__11,$__6]);});
$Language.$UHC.$JS.$JQuery.$JQuery.$Blur__=
 new _A_(new _F_(function()
                 {return {_tag_:0};}),[]);
$JCU.$_24okUNQ693=
 new _F_(function($_24x)
         {var $__=
           new _A_($UHC.$Base.$packedStringToString,["#txtAddRule"]);
          var $__3=
           [$__,$Language.$UHC.$JS.$JQuery.$JQuery.$Blur__,$JCU.$checkTermSyntax];
          var $__4=
           new _A_($UHC.$Base.$_3a,[$__3,$UHC.$Base.$_5b_5d]);
          var $__5=
           new _A_($UHC.$Base.$packedStringToString,["#txtAddRule"]);
          var $__6=
           [$__5,$Language.$UHC.$JS.$JQuery.$JQuery.$KeyPress__,$JCU.$clrUNQ657];
          var $__7=
           new _A_($UHC.$Base.$_3a,[$__6,$__4]);
          var $__8=
           new _A_($UHC.$Base.$packedStringToString,["#btnStartTerm"]);
          var $__9=
           [$__8,$Language.$UHC.$JS.$JQuery.$JQuery.$Click__,$JCU.$startExampleGoal];
          var $__10=
           new _A_($UHC.$Base.$_3a,[$__9,$__7]);
          var $__11=
           new _A_($UHC.$Base.$packedStringToString,["#btnLoadExampleData"]);
          var $__12=
           [$__11,$Language.$UHC.$JS.$JQuery.$JQuery.$Click__,$JCU.$loadExampleData];
          var $__13=
           new _A_($UHC.$Base.$_3a,[$__12,$__10]);
          var $__14=
           new _A_($UHC.$Base.$packedStringToString,["#btnReset"]);
          var $__15=
           [$__14,$Language.$UHC.$JS.$JQuery.$JQuery.$Click__,$JCU.$resetTreeUNQ664];
          var $__16=
           new _A_($UHC.$Base.$_3a,[$__15,$__13]);
          var $__17=
           new _A_($UHC.$Base.$packedStringToString,["#btnClearRules"]);
          var $__18=
           [$__17,$Language.$UHC.$JS.$JQuery.$JQuery.$Click__,$JCU.$clearRules];
          var $__19=
           new _A_($UHC.$Base.$_3a,[$__18,$__16]);
          var $__20=
           new _A_($UHC.$Base.$packedStringToString,["#btnAddRule"]);
          var $__21=
           [$__20,$Language.$UHC.$JS.$JQuery.$JQuery.$Click__,$JCU.$addRuleEvent];
          var $__22=
           new _A_($UHC.$Base.$_3a,[$__21,$__19]);
          var $__23=
           new _A_($JCU.$toggleClue,[$JCU.$emptyProof]);
          var $__24=
           new _A_($UHC.$Base.$packedStringToString,["#btnCheck"]);
          var $__25=
           [$__24,$Language.$UHC.$JS.$JQuery.$JQuery.$Click__,$__23];
          var $__26=
           new _A_($UHC.$Base.$_3a,[$__25,$__22]);
          var $__27=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$registerEvents,[$__26]);
          var $__28=
           new _A_($JCU.$__44__1148NEW517,[$_24x]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__28,$__27]);});
$JCU.$__44__1142=
 new _A_(new _F_(function()
                 {var $__=
                   new _A_($Data.$LocalStorage.$getLocalStorage,[$UHC.$Base.$__74__51__0,$JCU.$checkProofStoreKey]);
                  return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__,$JCU.$_24okUNQ693]);}),[]);
$Language.$UHC.$JS.$JQuery.$JQuery.$empty=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__3.empty());
          var $__5=
           _e_([]);
          return [$__2,$__5];});
$JCU.$_24okUNQ652=
 new _F_(function($_24x,$_24x2)
         {var $__=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$append,[$_24x,$_24x2]);
          var $__4=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$empty,[$_24x]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__4,$__]);});
$JCU.$__44__112=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,[""]);}),[]);
$JCU.$__44__111=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$JCU.$__44__112]);}),[]);
$JCU.$emptyProof=
 new _A_(new _F_(function()
                 {return new _A_($Data.$Tree.$Node__,[$JCU.$__44__111,$UHC.$Base.$_5b_5d]);}),[]);
$Language.$UHC.$JS.$Assorted.$__86__14=
 new _A_(new _F_(function()
                 {return new _A_($Language.$UHC.$JS.$Types.$toJS,[$Language.$UHC.$JS.$ECMA.$String.$ToJS__DCT40__2__0]);}),[]);
$Language.$UHC.$JS.$Assorted.$__alert=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_(alert($__3));
          var $__5=
           _e_([]);
          return [$__2,$__5];});
$Language.$UHC.$JS.$Assorted.$alert=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_2e,[$Language.$UHC.$JS.$Assorted.$__alert,$Language.$UHC.$JS.$Assorted.$__86__14]);}),[]);
$Util.$showError=
 new _A_(new _F_(function()
                 {return $Language.$UHC.$JS.$Assorted.$alert;}),[]);
$Data.$Map.$fromList=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$id;}),[]);
$Control.$Monad.$__120__30__0=
 new _F_(function($__,$x1,$xs,$fax)
         {return new _A_($Control.$Monad.$foldM,[$__,$x1,$fax,$xs]);});
$Control.$Monad.$foldM=
 new _F_(function($__,$x1,$x2,$x3)
         {var $x35=
           _e_($x3);
          var $__swJSW70__0;
          switch($x35._tag_)
           {case 0:
             var $__8=
              new _A_($x1,[$x2,$x35._1]);
             var $__9=
              new _A_($Control.$Monad.$__120__30__0,[$__,$x1,$x35._2]);
             var $__10=
              new _A_($UHC.$Base.$_3e_3e_3d,[$__,$__8,$__9]);
             $__swJSW70__0=
              $__10;
             break;
            case 1:
             var $__11=
              new _A_($UHC.$Base.$return,[$__,$x2]);
             $__swJSW70__0=
              $__11;
             break;}
          return $__swJSW70__0;});
$Language.$UHC.$JS.$JQuery.$JQuery.$findSelector_27=
 new _F_(function($__,$__2,$__3)
         {var $__4=
           _e_($__);
          var $__5=
           _e_($__2);
          var $__6=
           _e_($__4.find($__5));
          return [$__3,$__6];});
$Language.$UHC.$JS.$JQuery.$JQuery.$findSelector=
 new _F_(function($jq)
         {var $__=
           new _A_($Language.$UHC.$JS.$Types.$toJS,[$Language.$UHC.$JS.$ECMA.$String.$ToJS__DCT40__2__0]);
          var $__3=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$findSelector_27,[$jq]);
          return new _A_($UHC.$Base.$_2e,[$__3,$__]);});
$UHC.$Base.$__74__50__0DFLUHC_2eBase_2eshowsPrec=
 new _F_(function($d,$x__1)
         {var $x__13=
           _e_($x__1);
          var $__swJSW71__0;
          switch($x__13._tag_)
           {case 0:
             var $__=
              new _A_($UHC.$Base.$packedStringToString,["False"]);
             var $__5=
              new _A_($UHC.$Base.$showString,[$__]);
             $__swJSW71__0=
              $__5;
             break;
            case 1:
             var $__=
              new _A_($UHC.$Base.$packedStringToString,["True"]);
             var $__7=
              new _A_($UHC.$Base.$showString,[$__]);
             $__swJSW71__0=
              $__7;
             break;}
          return $__swJSW71__0;});
$UHC.$Base.$__74__50__0NEW5785UNQ9648EVLRDC=
 new _F_(function($__)
         {var $Show__=
           _e_(new _A_($UHC.$Base.$Show__CLS74__43__0,[$__]));
          var $__6=
           {_tag_:0,_1:$Show__._1,_2:$Show__._2,_3:$UHC.$Base.$__74__50__0DFLUHC_2eBase_2eshowsPrec};
          return $__6;});
$UHC.$Base.$__74__50__0NEW5783UNQ9647RDC=
 new _F_(function($__)
         {var $__2=
           new _A_($UHC.$Base.$__74__50__0NEW5785UNQ9648EVLRDC,[$__]);
          return $__2;});
$UHC.$Base.$__74__50__0UNQ9647RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$__74__50__0NEW5783UNQ9647RDC,[$UHC.$Base.$__74__50__0UNQ9647RDC]);}),[]);
$UHC.$Base.$__74__50__0=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$__74__50__0UNQ9647RDC;}),[]);
$UHC.$Base.$sequence__=
 new _F_(function($__)
         {var $__2=
           new _A_($UHC.$Base.$return,[$__,[]]);
          var $__3=
           new _A_($UHC.$Base.$_3e_3e,[$__]);
          return new _A_($UHC.$Base.$foldr,[$__3,$__2]);});
$UHC.$Base.$mapM__=
 new _F_(function($__,$f)
         {var $__3=
           new _A_($UHC.$Base.$map,[$f]);
          var $__4=
           new _A_($UHC.$Base.$sequence__,[$__]);
          return new _A_($UHC.$Base.$_2e,[$__4,$__3]);});
$Language.$UHC.$JS.$JQuery.$JQuery.$__bind=
 new _F_(function($__,$__2,$__3,$__4)
         {var $__5=
           _e_($__);
          var $__6=
           _e_($__2);
          var $__7=
           _e_($__3);
          var $__8=
           _e_($__5.bind($__6,$__7));
          var $__9=
           _e_([]);
          return [$__4,$__9];});
$Language.$UHC.$JS.$JQuery.$JQuery.$_24okUNQ805=
 new _F_(function($jq,$event,$_24x)
         {var $__=
           new _A_($UHC.$Base.$show,[$Language.$UHC.$JS.$JQuery.$JQuery.$Show__DCT124__4__0]);
          var $__5=
           new _A_($Language.$UHC.$JS.$Types.$toJS,[$Language.$UHC.$JS.$ECMA.$String.$ToJS__DCT40__2__0]);
          var $__6=
           new _A_($UHC.$Base.$_2e,[$__5,$__,$event]);
          return new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$__bind,[$jq,$__6,$_24x]);});
$Language.$UHC.$JS.$JQuery.$JQuery.$mkJEventHandler=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_(function(v1)
               {var res=
                 _e_(new _A_($__3,[v1,[]]));
                _e_(res[0]);
                return _e_(res[1]);});
          return [$__2,$__4];});
$Language.$UHC.$JS.$JQuery.$JQuery.$bind=
 new _F_(function($jq,$event,$eh)
         {var $__=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$mkJEventHandler,[$eh]);
          var $__5=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$_24okUNQ805,[$jq,$event]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__,$__5]);});
$Language.$UHC.$JS.$JQuery.$JQuery.$Show__DCT124__4__0DFLUHC_2eBase_2eshow=
 new _F_(function($x1)
         {var $__=
           _e_($x1);
          var $__swJSW73__0;
          switch($__._tag_)
           {case 0:
             var $__3=
              new _A_($UHC.$Base.$packedStringToString,["blur"]);
             $__swJSW73__0=
              $__3;
             break;
            case 1:
             var $__4=
              new _A_($UHC.$Base.$packedStringToString,["change"]);
             $__swJSW73__0=
              $__4;
             break;
            case 2:
             var $__5=
              new _A_($UHC.$Base.$packedStringToString,["click"]);
             $__swJSW73__0=
              $__5;
             break;
            case 3:
             var $__6=
              new _A_($UHC.$Base.$packedStringToString,["dblclick"]);
             $__swJSW73__0=
              $__6;
             break;
            case 4:
             var $__7=
              new _A_($UHC.$Base.$packedStringToString,["focus"]);
             $__swJSW73__0=
              $__7;
             break;
            case 5:
             var $__8=
              new _A_($UHC.$Base.$packedStringToString,["focusin"]);
             $__swJSW73__0=
              $__8;
             break;
            case 6:
             var $__9=
              new _A_($UHC.$Base.$packedStringToString,["focusout"]);
             $__swJSW73__0=
              $__9;
             break;
            case 7:
             var $__10=
              new _A_($UHC.$Base.$packedStringToString,["hover"]);
             $__swJSW73__0=
              $__10;
             break;
            case 8:
             var $__11=
              new _A_($UHC.$Base.$packedStringToString,["keydown"]);
             $__swJSW73__0=
              $__11;
             break;
            case 9:
             var $__12=
              new _A_($UHC.$Base.$packedStringToString,["keypress"]);
             $__swJSW73__0=
              $__12;
             break;
            case 10:
             var $__13=
              new _A_($UHC.$Base.$packedStringToString,["keyup"]);
             $__swJSW73__0=
              $__13;
             break;
            case 11:
             var $__14=
              new _A_($UHC.$Base.$packedStringToString,["mousedown"]);
             $__swJSW73__0=
              $__14;
             break;
            case 12:
             var $__15=
              new _A_($UHC.$Base.$packedStringToString,["mouseenter"]);
             $__swJSW73__0=
              $__15;
             break;
            case 13:
             var $__16=
              new _A_($UHC.$Base.$packedStringToString,["mouseleave"]);
             $__swJSW73__0=
              $__16;
             break;
            case 14:
             var $__17=
              new _A_($UHC.$Base.$packedStringToString,["mousemove"]);
             $__swJSW73__0=
              $__17;
             break;
            case 15:
             var $__18=
              new _A_($UHC.$Base.$packedStringToString,["mouseout"]);
             $__swJSW73__0=
              $__18;
             break;
            case 16:
             var $__19=
              new _A_($UHC.$Base.$packedStringToString,["mouseover"]);
             $__swJSW73__0=
              $__19;
             break;
            case 17:
             var $__20=
              new _A_($UHC.$Base.$packedStringToString,["mouseup"]);
             $__swJSW73__0=
              $__20;
             break;
            case 18:
             var $__21=
              new _A_($UHC.$Base.$packedStringToString,["ready"]);
             $__swJSW73__0=
              $__21;
             break;
            case 19:
             var $__22=
              new _A_($UHC.$Base.$packedStringToString,["resize"]);
             $__swJSW73__0=
              $__22;
             break;
            case 20:
             var $__23=
              new _A_($UHC.$Base.$packedStringToString,["scroll"]);
             $__swJSW73__0=
              $__23;
             break;
            case 21:
             var $__24=
              new _A_($UHC.$Base.$packedStringToString,["select"]);
             $__swJSW73__0=
              $__24;
             break;
            case 22:
             var $__25=
              new _A_($UHC.$Base.$packedStringToString,["submit"]);
             $__swJSW73__0=
              $__25;
             break;}
          return $__swJSW73__0;});
$Language.$UHC.$JS.$JQuery.$JQuery.$Show__NEW449UNQ968EVLDCT124__4__0RDC=
 new _F_(function($Show__)
         {var $Show__2=
           _e_(new _A_($UHC.$Base.$Show__CLS74__43__0,[$Show__]));
          var $__6=
           {_tag_:0,_1:$Language.$UHC.$JS.$JQuery.$JQuery.$Show__DCT124__4__0DFLUHC_2eBase_2eshow,_2:$Show__2._2,_3:$Show__2._3};
          return $__6;});
$Language.$UHC.$JS.$JQuery.$JQuery.$Show__NEW447UNQ967DCT124__4__0RDC=
 new _F_(function($Show__)
         {var $Show__2=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$Show__NEW449UNQ968EVLDCT124__4__0RDC,[$Show__]);
          return $Show__2;});
$Language.$UHC.$JS.$JQuery.$JQuery.$Show__UNQ967DCT124__4__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$Show__NEW447UNQ967DCT124__4__0RDC,[$Language.$UHC.$JS.$JQuery.$JQuery.$Show__UNQ967DCT124__4__0RDC]);}),[]);
$Language.$UHC.$JS.$JQuery.$JQuery.$Show__DCT124__4__0=
 new _A_(new _F_(function()
                 {return $Language.$UHC.$JS.$JQuery.$JQuery.$Show__UNQ967DCT124__4__0RDC;}),[]);
$Language.$UHC.$JS.$JQuery.$JQuery.$__unbind=
 new _F_(function($__,$__2,$__3)
         {var $__4=
           _e_($__);
          var $__5=
           _e_($__2);
          var $__6=
           _e_($__4.unbind($__5));
          var $__7=
           _e_([]);
          return [$__3,$__7];});
$Language.$UHC.$JS.$JQuery.$JQuery.$unbind=
 new _F_(function($jq)
         {var $__=
           new _A_($UHC.$Base.$show,[$Language.$UHC.$JS.$JQuery.$JQuery.$Show__DCT124__4__0]);
          var $__3=
           new _A_($Language.$UHC.$JS.$Types.$toJS,[$Language.$UHC.$JS.$ECMA.$String.$ToJS__DCT40__2__0]);
          var $__4=
           new _A_($UHC.$Base.$_2e,[$__3,$__]);
          var $__5=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$__unbind,[$jq]);
          return new _A_($UHC.$Base.$_2e,[$__5,$__4]);});
$Language.$UHC.$JS.$JQuery.$JQuery.$_24okUNQ959=
 new _F_(function($eh,$event,$_24x)
         {var $__=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$bind,[$_24x,$event,$eh]);
          var $__5=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$unbind,[$_24x,$event]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__5,$__]);});
$Language.$UHC.$JS.$JQuery.$JQuery.$__128__1343__0=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          var $__6=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$jQuery,[$__2[0]]);
          var $__7=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$_24okUNQ959,[$__2[2],$__2[1]]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__6,$__7]);});
$Language.$UHC.$JS.$JQuery.$JQuery.$registerEvents=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$mapM__,[$UHC.$Base.$Monad__DCT74__339__0,$Language.$UHC.$JS.$JQuery.$JQuery.$__128__1343__0]);}),[]);
$Language.$UHC.$JS.$JQuery.$JQuery.$append=
 new _A_(new _F_(function()
                 {return $Language.$UHC.$JS.$JQuery.$JQuery.$__append;}),[]);
$Language.$UHC.$JS.$JQuery.$Droppable.$Droppable__=
 new _F_(function($x1,$x2)
         {return {_tag_:0,hoverClass:$x1,drop:$x2};});
$Language.$UHC.$JS.$JQuery.$JQuery.$valJSString=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__3.val());
          return [$__2,$__4];});
$Language.$UHC.$JS.$JQuery.$JQuery.$valString=
 new _F_(function($jq)
         {var $__=
           new _A_($Language.$UHC.$JS.$Types.$fromJS,[$Language.$UHC.$JS.$ECMA.$String.$FromJS__DCT40__4__0]);
          var $__3=
           new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0]);
          var $__4=
           new _A_($UHC.$Base.$_2e,[$__3,$__]);
          var $__5=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$valJSString,[$jq]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__5,$__4]);});
$Language.$UHC.$JS.$JQuery.$JQuery.$_24okUNQ934=
 new _F_(function($f,$jq,$_24x)
         {return new _A_($f,[$_24x,$jq]);});
$Language.$UHC.$JS.$JQuery.$JQuery.$gUNQ930=
 new _F_(function($f,$this,$jq)
         {var $__=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$jQueryObj,[$this]);
          var $__5=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$_24okUNQ934,[$f,$jq]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__,$__5]);});
$Language.$UHC.$JS.$JQuery.$JQuery.$__mkJThisEventHandler=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_(function(v1,v2)
               {var res=
                 _e_(new _A_($__3,[v1,v2,[]]));
                _e_(res[0]);
                return _e_(res[1]);});
          return [$__2,$__4];});
$Language.$UHC.$JS.$JQuery.$JQuery.$mkJThisEventHandler=
 new _F_(function($f)
         {var $__=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$gUNQ930,[$f]);
          return new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$__mkJThisEventHandler,[$__]);});
$Templates.$statusClassUNQ7=
 new _F_(function($x1)
         {var $__=
           _e_($x1);
          var $__swJSW76__0;
          switch($__._tag_)
           {case 0:
             var $__3=
              new _A_($UHC.$Base.$packedStringToString,["greenField"]);
             $__swJSW76__0=
              $__3;
             break;
            case 1:
             var $__4=
              new _A_($UHC.$Base.$packedStringToString,["yellowField"]);
             $__swJSW76__0=
              $__4;
             break;
            case 2:
             var $__5=
              new _A_($UHC.$Base.$packedStringToString,["redField"]);
             $__swJSW76__0=
              $__5;
             break;}
          return $__swJSW76__0;});
$Templates.$disabled_27NEW6UNQ8=
 new _F_(function($disabled)
         {var $__=
           _e_($disabled);
          var $__swJSW77__0;
          switch($__._tag_)
           {case 0:
             var $__3=
              new _A_($UHC.$Base.$packedStringToString,[""]);
             $__swJSW77__0=
              $__3;
             break;
            case 1:
             var $__4=
              new _A_($UHC.$Base.$packedStringToString,[" disabled=\"disabled\""]);
             $__swJSW77__0=
              $__4;
             break;}
          return $__swJSW77__0;});
$Templates.$proof__tree__item=
 new _F_(function($term,$treeLbl,$disabled,$status)
         {var $disabled_27=
           new _A_($Templates.$disabled_27NEW6UNQ8,[$disabled]);
          var $__=
           new _A_($UHC.$Base.$packedStringToString,[" /></div>"]);
          var $__7=
           new _A_($UHC.$Base.$_2b_2b,[$disabled_27,$__]);
          var $__8=
           new _A_($UHC.$Base.$packedStringToString,["\""]);
          var $__9=
           new _A_($UHC.$Base.$_2b_2b,[$__8,$__7]);
          var $__10=
           new _A_($UHC.$Base.$_2b_2b,[$term,$__9]);
          var $__11=
           new _A_($UHC.$Base.$packedStringToString,["\" value=\""]);
          var $__12=
           new _A_($UHC.$Base.$_2b_2b,[$__11,$__10]);
          var $__13=
           new _A_($UHC.$Base.$_2b_2b,[$treeLbl,$__12]);
          var $__14=
           new _A_($UHC.$Base.$packedStringToString,["\" id=\"proof_"]);
          var $__15=
           new _A_($UHC.$Base.$_2b_2b,[$__14,$__13]);
          var $__16=
           new _A_($Templates.$statusClassUNQ7,[$status]);
          var $__17=
           new _A_($UHC.$Base.$_2b_2b,[$__16,$__15]);
          var $__18=
           new _A_($UHC.$Base.$packedStringToString,[". <input type=\"text\" class=\"droppable "]);
          var $__19=
           new _A_($UHC.$Base.$_2b_2b,[$__18,$__17]);
          var $__20=
           new _A_($UHC.$Base.$_2b_2b,[$treeLbl,$__19]);
          var $__21=
           new _A_($UHC.$Base.$packedStringToString,["<div class=\"tree_item dropzone\">  "]);
          return new _A_($UHC.$Base.$_2b_2b,[$__21,$__20]);});
$UHC.$Base.$nNEW5950UNQ7196CCN=
 new _F_(function($x1,$x2)
         {var $x23=
           _e_($x2);
          var $__swJSW78__0;
          switch($x23._tag_)
           {case 0:
             var $__6=
              new _A_($UHC.$Base.$_2d,[$UHC.$Base.$Num__DCT74__101__0,$x1,1]);
             var $__7=
              new _A_($UHC.$Base.$drop,[$__6,$x23._2]);
             $__swJSW78__0=
              $__7;
             break;
            case 1:
             $__swJSW78__0=
              $UHC.$Base.$_5b_5d;
             break;}
          return $__swJSW78__0;});
$UHC.$Base.$drop=
 new _F_(function($x1,$x2)
         {var $n=
           new _A_($UHC.$Base.$nNEW5950UNQ7196CCN,[$x1,$x2]);
          var $__=
           new _A_($UHC.$Base.$_3c_3d,[$UHC.$Base.$Ord__DCT74__91__0,$x1,0]);
          var $__5=
           _e_($__);
          var $__swJSW79__0;
          switch($__5._tag_)
           {case 0:
             $__swJSW79__0=
              $n;
             break;
            case 1:
             $__swJSW79__0=
              $x2;
             break;}
          return $__swJSW79__0;});
$UHC.$Base.$nNEW5936UNQ7170CCN=
 new _F_(function($x1,$x2)
         {var $x23=
           _e_($x2);
          var $__swJSW80__0;
          switch($x23._tag_)
           {case 0:
             var $__=
              new _A_($UHC.$Base.$_2d,[$UHC.$Base.$Num__DCT74__101__0,$x1,1]);
             var $__7=
              new _A_($UHC.$Base.$take,[$__,$x23._2]);
             var $__8=
              new _A_($UHC.$Base.$_3a,[$x23._1,$__7]);
             $__swJSW80__0=
              $__8;
             break;
            case 1:
             $__swJSW80__0=
              $UHC.$Base.$_5b_5d;
             break;}
          return $__swJSW80__0;});
$UHC.$Base.$take=
 new _F_(function($x1,$x2)
         {var $n=
           new _A_($UHC.$Base.$nNEW5936UNQ7170CCN,[$x1,$x2]);
          var $__=
           new _A_($UHC.$Base.$_3c_3d,[$UHC.$Base.$Ord__DCT74__91__0,$x1,0]);
          var $__5=
           _e_($__);
          var $__swJSW81__0;
          switch($__5._tag_)
           {case 0:
             $__swJSW81__0=
              $n;
             break;
            case 1:
             $__swJSW81__0=
              $UHC.$Base.$_5b_5d;
             break;}
          return $__swJSW81__0;});
$Prolog.$insertNode=
 new _F_(function($x1,$x2,$x3)
         {var $x14=
           _e_($x1);
          var $x27=
           _e_($x2);
          var $__swJSW83__0;
          switch($x27._tag_)
           {case 0:
             var $__=
              new _A_($UHC.$Base.$drop,[$x27._1,$x14.subForest]);
             var $__11=
              new _A_($UHC.$Base.$_2d,[$UHC.$Base.$Num__DCT74__101__0,$x27._1,1]);
             var $__12=
              new _A_($UHC.$Base.$_21_21,[$x14.subForest,$__11]);
             var $__13=
              new _A_($Prolog.$insertNode,[$__12,$x27._2,$x3]);
             var $__14=
              new _A_($UHC.$Base.$_3a,[$__13,$__]);
             var $__15=
              new _A_($UHC.$Base.$_2d,[$UHC.$Base.$Num__DCT74__101__0,$x27._1,1]);
             var $__16=
              new _A_($UHC.$Base.$take,[$__15,$x14.subForest]);
             var $__17=
              new _A_($UHC.$Base.$_2b_2b,[$__16,$__14]);
             var $__18=
              new _A_($Data.$Tree.$Node__,[$x14.rootLabel,$__17]);
             $__swJSW83__0=
              $__18;
             break;
            case 1:
             var $__=
              new _A_($Data.$Tree.$Node__,[$x14.rootLabel,$x3]);
             $__swJSW83__0=
              $__;
             break;}
          return $__swJSW83__0;});
$Prolog.$mkPrf_27UNQ344=
 new _F_(function($x1,$ns,$ncs,$env)
         {var $__=
           new _A_($Prolog.$insertNode,[$x1,$ns,$ncs]);
          return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$subst,[$Prolog.$Subst__DCT28__3__0,$env,$__]);});
$Prolog.$__30__6438__0NEW751UNQ346=
 new _F_(function($tmnd)
         {var $__=
           _e_($tmnd);
          var $__swJSW84__0;
          switch($__._tag_)
           {case 0:
             $__swJSW84__0=
              $__._1;
             break;
            case 1:
             $__swJSW84__0=
              $UHC.$Base.$undefined;
             break;}
          return $__swJSW84__0;});
$UHC.$Base.$primIntegerToPackedString=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return $__2.toString();});
$UHC.$Base.$Show__DCT74__157__0DFLUHC_2eBase_2eshow=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_2e,[$UHC.$Base.$packedStringToString,$UHC.$Base.$primIntegerToPackedString]);}),[]);
$UHC.$Base.$Show__NEW5756UNQ11694EVLDCT74__157__0RDC=
 new _F_(function($Show__,$Show__2)
         {var $Show__3=
           _e_(new _A_($UHC.$Base.$Show__CLS74__43__0,[$Show__2]));
          var $__7=
           {_tag_:0,_1:$Show__,_2:$Show__3._2,_3:$Show__3._3};
          return $__7;});
$UHC.$Base.$Show__NEW5753UNQ11693DCT74__157__0RDC=
 new _F_(function($Show__,$Show__2)
         {var $Show__3=
           new _A_($UHC.$Base.$Show__NEW5756UNQ11694EVLDCT74__157__0RDC,[$Show__,$Show__2]);
          return $Show__3;});
$UHC.$Base.$Show__UNQ11693DCT74__157__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Show__NEW5753UNQ11693DCT74__157__0RDC,[$UHC.$Base.$Show__DCT74__157__0DFLUHC_2eBase_2eshow,$UHC.$Base.$Show__UNQ11693DCT74__157__0RDC]);}),[]);
$UHC.$Base.$Show__DCT74__157__0=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$Show__UNQ11693DCT74__157__0RDC;}),[]);
$UHC.$Base.$__78__12917=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$show,[$UHC.$Base.$Show__DCT74__157__0]);}),[]);
$UHC.$Base.$__78__12918=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$toInteger,[$UHC.$Base.$Integral__DCT74__110__0]);}),[]);
$UHC.$Base.$Show__DCT74__128__0DFLUHC_2eBase_2eshow=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_2e,[$UHC.$Base.$__78__12917,$UHC.$Base.$__78__12918]);}),[]);
$UHC.$Base.$Show__NEW6397UNQ11688EVLDCT74__128__0RDC=
 new _F_(function($Show__,$Show__2)
         {var $Show__3=
           _e_(new _A_($UHC.$Base.$Show__CLS74__43__0,[$Show__]));
          var $__7=
           {_tag_:0,_1:$Show__2,_2:$Show__3._2,_3:$Show__3._3};
          return $__7;});
$UHC.$Base.$Show__NEW6394UNQ11685DCT74__128__0RDC=
 new _F_(function($Show__,$Show__2)
         {var $Show__3=
           new _A_($UHC.$Base.$Show__NEW6397UNQ11688EVLDCT74__128__0RDC,[$Show__,$Show__2]);
          return $Show__3;});
$UHC.$Base.$Show__UNQ11685DCT74__128__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Show__NEW6394UNQ11685DCT74__128__0RDC,[$UHC.$Base.$Show__UNQ11685DCT74__128__0RDC,$UHC.$Base.$Show__DCT74__128__0DFLUHC_2eBase_2eshow]);}),[]);
$UHC.$Base.$Show__DCT74__128__0=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$Show__UNQ11685DCT74__128__0RDC;}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$Taggable__DCT52__6__0DFLLanguage_2eProlog_2eNanoProlog_2eNanoProlog_2etag=
 new _F_(function($__,$n)
         {var $__3=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$tag,[$__,$n]);
          return new _A_($UHC.$Base.$map,[$__3]);});
$Language.$Prolog.$NanoProlog.$NanoProlog.$Taggable__NEW101UNQ936EVLDCT52__6__0RDC=
 new _F_(function($__,$Taggable__)
         {var $Taggable__3=
           _e_(new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Taggable__CLS52__3__0,[$Taggable__]));
          var $__5=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Taggable__DCT52__6__0DFLLanguage_2eProlog_2eNanoProlog_2eNanoProlog_2etag,[$__]);
          var $__6=
           {_tag_:0,_1:$__5};
          return $__6;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$Taggable__NEW98UNQ934DCT52__6__0RDC=
 new _F_(function($__,$Taggable__)
         {var $Taggable__3=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Taggable__NEW101UNQ936EVLDCT52__6__0RDC,[$__,$Taggable__]);
          return $Taggable__3;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$Taggable__DCT52__6__0=
 new _F_(function($__)
         {var $Taggable__=
           _i_();
          _i_set_($Taggable__,new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Taggable__NEW98UNQ934DCT52__6__0RDC,[$__,$Taggable__]));
          return $Taggable__;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$Taggable__DCT52__4__0DFLLanguage_2eProlog_2eNanoProlog_2eNanoProlog_2etag=
 new _F_(function($__,$x1,$x2)
         {var $x24=
           _e_($x2);
          var $__swJSW88__0;
          switch($x24._tag_)
           {case 0:
             var $__7=
              new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$tag,[$__,$x1,$x24._2]);
             var $__8=
              new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$x24._1,$__7]);
             $__swJSW88__0=
              $__8;
             break;
            case 1:
             var $__10=
              new _A_($UHC.$Base.$_2b_2b,[$x24._1,$x1]);
             var $__11=
              new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$__10]);
             $__swJSW88__0=
              $__11;
             break;}
          return $__swJSW88__0;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$Taggable__CLS52__3__0=
 new _F_(function($Taggable__)
         {var $Taggable__2=
           {_tag_:0,_1:$UHC.$Base.$undefined};
          return $Taggable__2;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$Taggable__NEW110UNQ910EVLDCT52__4__0RDC=
 new _F_(function($Taggable__,$__)
         {var $Taggable__3=
           _e_(new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Taggable__CLS52__3__0,[$Taggable__]));
          var $__5=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Taggable__DCT52__4__0DFLLanguage_2eProlog_2eNanoProlog_2eNanoProlog_2etag,[$__]);
          var $__6=
           {_tag_:0,_1:$__5};
          return $__6;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$Taggable__NEW107UNQ908DCT52__4__0RDC=
 new _F_(function($Taggable__,$__)
         {var $Taggable__3=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Taggable__NEW110UNQ910EVLDCT52__4__0RDC,[$Taggable__,$__]);
          return $Taggable__3;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$Taggable__UNQ908DCT52__4__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Taggable__NEW107UNQ908DCT52__4__0RDC,[$Language.$Prolog.$NanoProlog.$NanoProlog.$Taggable__UNQ908DCT52__4__0RDC,$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__4420__2__0UNQ909]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__4420__2__0UNQ909=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Taggable__DCT52__6__0,[$Language.$Prolog.$NanoProlog.$NanoProlog.$Taggable__UNQ908DCT52__4__0RDC]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$Taggable__DCT52__4__0=
 new _A_(new _F_(function()
                 {return $Language.$Prolog.$NanoProlog.$NanoProlog.$Taggable__UNQ908DCT52__4__0RDC;}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__428__0NEW552UNQ218CCN=
 new _F_(function($x1,$x2)
         {var $x13=
           _e_($x1);
          var $x26=
           _e_($x2);
          var $__swJSW91__0;
          switch($x26._tag_)
           {case 0:
             var $__=
              new _A_($UHC.$Base.$Eq__DCT74__394__0,[$UHC.$Base.$Eq__DCT74__56__0]);
             var $__9=
              new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$subst,[$Language.$Prolog.$NanoProlog.$NanoProlog.$Subst__DCT52__10__0,$x26._1,$x13[1]]);
             var $__10=
              new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$subst,[$Language.$Prolog.$NanoProlog.$NanoProlog.$Subst__DCT52__10__0,$x26._1,$x13[0]]);
             $__swJSW91__0=
              new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$uniUNQ236,[$x26,$x26._1,$__,$__10,$__9]);
             break;
            case 1:
             $__swJSW91__0=
              $UHC.$Base.$undefined;
             break;}
          return $__swJSW91__0;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$uniUNQ236=
 new _F_(function($x2,$e,$__,$x1,$x25)
         {var $__6=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$__54__533__0NEW559UNQ251CCN,[$x2,$e,$__,$x1,$x25]);
          var $x17=
           _e_($x1);
          var $__swJSW92__0;
          switch($x17._tag_)
           {case 0:
             $__swJSW92__0=
              $__6;
             break;
            case 1:
             var $__11=
              new _A_($Data.$Map.$insert,[$x17._1,$x25,$e]);
             var $__12=
              new _A_($UHC.$Base.$Just__,[$__11]);
             $__swJSW92__0=
              $__12;
             break;}
          return $__swJSW92__0;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__533__0NEW559UNQ251CCN=
 new _F_(function($x2,$e,$__,$x1,$x25)
         {var $x=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$xNEW565UNQ252CCN,[$x2,$__,$x1,$x25]);
          var $x27=
           _e_($x25);
          var $__swJSW93__0;
          switch($x27._tag_)
           {case 0:
             $__swJSW93__0=
              $x;
             break;
            case 1:
             var $__11=
              new _A_($Data.$Map.$insert,[$x27._1,$x1,$e]);
             var $__12=
              new _A_($UHC.$Base.$Just__,[$__11]);
             $__swJSW93__0=
              $__12;
             break;}
          return $__swJSW93__0;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$xNEW565UNQ252CCN=
 new _F_(function($x2,$__,$x1,$x24)
         {var $x15=
           _e_($x1);
          var $__swJSW94__0;
          switch($x15._tag_)
           {case 0:
             var $x28=
              _e_($x24);
             var $__swJSW95__0;
             switch($x28._tag_)
              {case 0:
                var $__11=
                 new _A_($UHC.$Base.$length,[$x28._2]);
                var $__12=
                 new _A_($UHC.$Base.$length,[$x15._2]);
                var $__13=
                 new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__88__0,$__12,$__11]);
                var $__14=
                 new _A_($UHC.$Base.$_3d_3d,[$__,$x15._1,$x28._1]);
                var $__15=
                 new _A_($UHC.$Base.$_26_26,[$__14,$__13]);
                var $__16=
                 _e_($__15);
                var $__swJSW96__0;
                switch($__16._tag_)
                 {case 0:
                   var $__17=
                    _e_($UHC.$Base.$otherwise);
                   var $__swJSW97__0;
                   switch($__17._tag_)
                    {case 0:
                      $__swJSW97__0=
                       $UHC.$Base.$undefined;
                      break;
                     case 1:
                      $__swJSW97__0=
                       $UHC.$Base.$Nothing__;
                      break;}
                   $__swJSW96__0=
                    $__swJSW97__0;
                   break;
                  case 1:
                   var $__18=
                    new _A_($UHC.$Base.$zip,[$x15._2,$x28._2]);
                   var $__19=
                    new _A_($UHC.$Base.$foldr,[$Language.$Prolog.$NanoProlog.$NanoProlog.$unify,$x2,$__18]);
                   $__swJSW96__0=
                    $__19;
                   break;}
                $__swJSW95__0=
                 $__swJSW96__0;
                break;
               case 1:
                $__swJSW95__0=
                 $UHC.$Base.$undefined;
                break;}
             $__swJSW94__0=
              $__swJSW95__0;
             break;
            case 1:
             $__swJSW94__0=
              $UHC.$Base.$undefined;
             break;}
          return $__swJSW94__0;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$unify=
 new _F_(function($x1,$x2)
         {var $__=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$__54__428__0NEW552UNQ218CCN,[$x1,$x2]);
          var $x24=
           _e_($x2);
          var $__swJSW98__0;
          switch($x24._tag_)
           {case 0:
             $__swJSW98__0=
              $__;
             break;
            case 1:
             $__swJSW98__0=
              $UHC.$Base.$Nothing__;
             break;}
          return $__swJSW98__0;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$tag=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._1;});
$Prolog.$tmNEW754UNQ347=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return $__2.rootLabel;});
$Prolog.$drprsNEW736UNQ334=
 new _F_(function($x1,$x2,$ns,$tmnd,$ts,$t)
         {var $__=
           new _A_($UHC.$Base.$show,[$UHC.$Base.$Show__DCT74__128__0]);
          var $__8=
           new _A_($UHC.$Base.$concatMap,[$__,$x2]);
          var $__9=
           new _A_($Data.$List.$intersperse,[46]);
          var $ntg=
           new _A_($UHC.$Base.$_24,[$__9,$__8]);
          var $__11=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Taggable__DCT52__6__0,[$Language.$Prolog.$NanoProlog.$NanoProlog.$Taggable__DCT52__4__0]);
          var $__12=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$tag,[$__11,$ntg,$ts]);
          var $__13=
           new _A_($UHC.$Base.$flip,[$Data.$Tree.$Node__,$UHC.$Base.$_5b_5d]);
          var $ncs=
           new _A_($UHC.$Base.$map,[$__13,$__12]);
          var $__15=
           new _A_($Prolog.$__30__6438__0NEW751UNQ346,[$tmnd]);
          var $tm=
           new _A_($Prolog.$tmNEW754UNQ347,[$__15]);
          var $__17=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$tag,[$Language.$Prolog.$NanoProlog.$NanoProlog.$Taggable__DCT52__4__0,$ntg,$t]);
          var $__18=
           [$__17,$tm];
          var $__19=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$unify,[$__18,$Language.$Prolog.$NanoProlog.$NanoProlog.$emptyEnv]);
          var $__20=
           _e_($__19);
          var $__swJSW101__0;
          switch($__20._tag_)
           {case 0:
             var $__22=
              new _A_($Prolog.$mkPrf_27UNQ344,[$x1,$ns,$ncs,$__20._1]);
             var $__23=
              new _A_($Prolog.$DropRes__,[$UHC.$Base.$True__,$__22]);
             $__swJSW101__0=
              $__23;
             break;
            case 1:
             var $__24=
              new _A_($Prolog.$DropRes__,[$UHC.$Base.$False__,$x1]);
             $__swJSW101__0=
              $__24;
             break;}
          return $__swJSW101__0;});
$UHC.$Base.$_3c=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._1;});
$UHC.$Base.$xsNEW5627UNQ7337CCN=
 new _F_(function($x1,$x2)
         {var $x13=
           _e_($x1);
          var $__swJSW103__0;
          switch($x13._tag_)
           {case 0:
             var $__6=
              new _A_($UHC.$Base.$_2d,[$UHC.$Base.$Num__DCT74__101__0,$x2,1]);
             var $__7=
              new _A_($UHC.$Base.$_21_21,[$x13._2,$__6]);
             var $x28=
              _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__88__0,0,$x2]));
             var $__swJSW104__0;
             switch($x28._tag_)
              {case 0:
                $__swJSW104__0=
                 $__7;
                break;
               case 1:
                $__swJSW104__0=
                 $x13._1;
                break;}
             $__swJSW103__0=
              $__swJSW104__0;
             break;
            case 1:
             var $__=
              new _A_($UHC.$Base.$packedStringToString,["Prelude.!!: index too large"]);
             var $__10=
              new _A_($UHC.$Base.$error,[$__]);
             $__swJSW103__0=
              $__10;
             break;}
          return $__swJSW103__0;});
$UHC.$Base.$_21_21=
 new _F_(function($x1,$x2)
         {var $xs=
           new _A_($UHC.$Base.$xsNEW5627UNQ7337CCN,[$x1,$x2]);
          var $__=
           new _A_($UHC.$Base.$_3c,[$UHC.$Base.$Ord__DCT74__91__0,$x2,0]);
          var $__5=
           _e_($__);
          var $__swJSW105__0;
          switch($__5._tag_)
           {case 0:
             $__swJSW105__0=
              $xs;
             break;
            case 1:
             var $__6=
              new _A_($UHC.$Base.$packedStringToString,["Prelude.!!: negative index"]);
             var $__7=
              new _A_($UHC.$Base.$error,[$__6]);
             $__swJSW105__0=
              $__7;
             break;}
          return $__swJSW105__0;});
$Prolog.$__30__5546__0NEW680UNQ246CCN=
 new _F_(function($x1,$x2)
         {var $x23=
           _e_($x2);
          var $__swJSW106__0;
          switch($x23._tag_)
           {case 0:
             $__swJSW106__0=
              $UHC.$Base.$undefined;
             break;
            case 1:
             var $__=
              new _A_($UHC.$Base.$Just__,[$x1]);
             $__swJSW106__0=
              $__;
             break;}
          return $__swJSW106__0;});
$Prolog.$__30__5552__0NEW686UNQ254CCN=
 new _F_(function($x2,$__,$__3)
         {var $x24=
           _e_($x2);
          var $__swJSW107__0;
          switch($x24._tag_)
           {case 0:
             var $__7=
              new _A_($UHC.$Base.$length,[$__3]);
             var $__8=
              new _A_($UHC.$Base.$_3e_3d,[$UHC.$Base.$Ord__DCT74__91__0,$__7,$x24._1]);
             var $__9=
              _e_($__8);
             var $__swJSW108__0;
             switch($__9._tag_)
              {case 0:
                var $__10=
                 _e_($UHC.$Base.$otherwise);
                var $__swJSW109__0;
                switch($__10._tag_)
                 {case 0:
                   $__swJSW109__0=
                    $__;
                   break;
                  case 1:
                   $__swJSW109__0=
                    $UHC.$Base.$Nothing__;
                   break;}
                $__swJSW108__0=
                 $__swJSW109__0;
                break;
               case 1:
                var $__11=
                 new _A_($UHC.$Base.$_2d,[$UHC.$Base.$Num__DCT74__101__0,$x24._1,1]);
                var $__12=
                 new _A_($UHC.$Base.$_21_21,[$__3,$__11]);
                var $__13=
                 new _A_($Prolog.$getNode,[$__12,$x24._2]);
                $__swJSW108__0=
                 $__13;
                break;}
             $__swJSW107__0=
              $__swJSW108__0;
             break;
            case 1:
             $__swJSW107__0=
              $__;
             break;}
          return $__swJSW107__0;});
$Prolog.$getNode=
 new _F_(function($x1,$x2)
         {var $__=
           new _A_($Prolog.$__30__5546__0NEW680UNQ246CCN,[$x1,$x2]);
          var $x14=
           _e_($x1);
          var $__7=
           new _A_($Prolog.$__30__5552__0NEW686UNQ254CCN,[$x2,$__,$x14.subForest]);
          var $__8=
           _e_($x14.subForest);
          var $__swJSW111__0;
          switch($__8._tag_)
           {case 0:
             $__swJSW111__0=
              $__7;
             break;
            case 1:
             var $x211=
              _e_($x2);
             var $__swJSW112__0;
             switch($x211._tag_)
              {case 0:
                $__swJSW112__0=
                 $UHC.$Base.$Nothing__;
                break;
               case 1:
                $__swJSW112__0=
                 $__7;
                break;}
             $__swJSW111__0=
              $__swJSW112__0;
             break;}
          return $__swJSW111__0;});
$Prolog.$prfNEW729UNQ320CCN=
 new _F_(function($x1,$x2,$x3)
         {var $x24=
           _e_($x2);
          var $__swJSW113__0;
          switch($x24._tag_)
           {case 0:
             var $x37=
              _e_($x3);
             var $tmnd=
              new _A_($Prolog.$getNode,[$x1,$x24._2]);
             var $drprs=
              new _A_($Prolog.$drprsNEW736UNQ334,[$x1,$x24,$x24._2,$tmnd,$x37._2,$x37._1]);
             var $__12=
              new _A_($Prolog.$isNothing,[$tmnd]);
             var $__13=
              _e_($__12);
             var $__swJSW115__0;
             switch($__13._tag_)
              {case 0:
                var $__14=
                 _e_($UHC.$Base.$otherwise);
                var $__swJSW116__0;
                switch($__14._tag_)
                 {case 0:
                   $__swJSW116__0=
                    $UHC.$Base.$undefined;
                   break;
                  case 1:
                   $__swJSW116__0=
                    $drprs;
                   break;}
                $__swJSW115__0=
                 $__swJSW116__0;
                break;
               case 1:
                var $__15=
                 new _A_($Prolog.$DropRes__,[$UHC.$Base.$False__,$x1]);
                $__swJSW115__0=
                 $__15;
                break;}
             $__swJSW113__0=
              $__swJSW115__0;
             break;
            case 1:
             $__swJSW113__0=
              $UHC.$Base.$undefined;
             break;}
          return $__swJSW113__0;});
$Prolog.$DropRes__=
 new _F_(function($x1,$x2)
         {return {_tag_:0,_1:$x1,_2:$x2};});
$Prolog.$dropUnify=
 new _F_(function($x1,$x2,$x3)
         {var $prf=
           new _A_($Prolog.$prfNEW729UNQ320CCN,[$x1,$x2,$x3]);
          var $x25=
           _e_($x2);
          var $__swJSW117__0;
          switch($x25._tag_)
           {case 0:
             $__swJSW117__0=
              $prf;
             break;
            case 1:
             var $__=
              new _A_($Prolog.$DropRes__,[$UHC.$Base.$False__,$x1]);
             $__swJSW117__0=
              $__;
             break;}
          return $__swJSW117__0;});
$Language.$UHC.$JS.$JQuery.$JQuery.$wrappedJQueryEvent=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_(wrappedThis($__3));
          return [$__2,$__4];});
$Language.$UHC.$JS.$Primitives.$__getAttr=
 new _F_(function($__,$__2,$__3)
         {var $__4=
           _e_($__);
          var $__5=
           _e_($__2);
          var $__6=
           _e_(primGetAttr($__4,$__5));
          return [$__3,$__6];});
$Language.$UHC.$JS.$Primitives.$getAttr=
 new _F_(function($s)
         {var $__=
           new _A_($Language.$UHC.$JS.$Types.$toJS,[$Language.$UHC.$JS.$ECMA.$String.$ToJS__DCT40__2__0,$s]);
          return new _A_($Language.$UHC.$JS.$Primitives.$__getAttr,[$__]);});
$Language.$Prolog.$NanoProlog.$NanoProlog.$showCommas=
 new _F_(function($__,$l)
         {var $__3=
           new _A_($UHC.$Base.$show,[$__]);
          var $__4=
           new _A_($UHC.$Base.$map,[$__3,$l]);
          var $__5=
           new _A_($UHC.$Base.$packedStringToString,[", "]);
          return new _A_($Data.$List.$intercalate,[$__5,$__4]);});
$Language.$Prolog.$NanoProlog.$NanoProlog.$hNEW171UNQ597CCN=
 new _F_(function($Show__,$__,$h,$__4)
         {var $__5=
           _e_($__4);
          var $__swJSW118__0;
          switch($__5._tag_)
           {case 0:
             var $__8=
              _e_($__5._2);
             var $__swJSW119__0;
             switch($__8._tag_)
              {case 0:
                $__swJSW119__0=
                 $__;
                break;
               case 1:
                var $__11=
                 new _A_($UHC.$Base.$show,[$Show__,$__5._1]);
                var $__12=
                 new _A_($UHC.$Base.$packedStringToString,[":"]);
                var $__13=
                 new _A_($UHC.$Base.$_2b_2b,[$__12,$__11]);
                var $__14=
                 new _A_($UHC.$Base.$show,[$Show__,$h]);
                var $__15=
                 new _A_($UHC.$Base.$_2b_2b,[$__14,$__13]);
                $__swJSW119__0=
                 $__15;
                break;}
             $__swJSW118__0=
              $__swJSW119__0;
             break;
            case 1:
             $__swJSW118__0=
              $__;
             break;}
          return $__swJSW118__0;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$fNEW233UNQ676CCN=
 new _F_(function($Show__,$__,$__3,$f)
         {var $__5=
           _e_($__3);
          var $__swJSW120__0;
          switch($__5._tag_)
           {case 0:
             var $__8=
              _e_($__5._2);
             var $__swJSW121__0;
             switch($__8._tag_)
              {case 0:
                $__swJSW121__0=
                 $__;
                break;
               case 1:
                var $__11=
                 new _A_($UHC.$Base.$show,[$Show__,$__5._1]);
                var $__12=
                 new _A_($UHC.$Base.$packedStringToString,[" -> "]);
                var $__13=
                 new _A_($UHC.$Base.$_2b_2b,[$__12,$__11]);
                var $__14=
                 new _A_($UHC.$Base.$show,[$Show__,$f]);
                var $__15=
                 new _A_($UHC.$Base.$_2b_2b,[$__14,$__13]);
                $__swJSW121__0=
                 $__15;
                break;}
             $__swJSW120__0=
              $__swJSW121__0;
             break;
            case 1:
             $__swJSW120__0=
              $__;
             break;}
          return $__swJSW120__0;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$iNEW149UNQ569CCN=
 new _F_(function($Show__,$i,$__)
         {var $__4=
           new _A_($UHC.$Base.$packedStringToString,[")"]);
          var $__5=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$showCommas,[$Show__,$__]);
          var $__6=
           new _A_($UHC.$Base.$_2b_2b,[$__5,$__4]);
          var $__7=
           new _A_($UHC.$Base.$packedStringToString,["("]);
          var $__8=
           new _A_($UHC.$Base.$_2b_2b,[$__7,$__6]);
          var $__9=
           new _A_($UHC.$Base.$_2b_2b,[$i,$__8]);
          var $i10=
           _e_($i);
          var $__swJSW122__0;
          switch($i10._tag_)
           {case 0:
             var $__13=
              _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,45,$i10._1]));
             var $__swJSW123__0;
             switch($__13._tag_)
              {case 0:
                var $__14=
                 _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,91,$i10._1]));
                var $__swJSW124__0;
                switch($__14._tag_)
                 {case 0:
                   var $__15=
                    _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,99,$i10._1]));
                   var $__swJSW125__0;
                   switch($__15._tag_)
                    {case 0:
                      $__swJSW125__0=
                       $__9;
                      break;
                     case 1:
                      var $__16=
                       _e_($i10._2);
                      var $__swJSW126__0;
                      switch($__16._tag_)
                       {case 0:
                         var $__19=
                          _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,111,$__16._1]));
                         var $__swJSW127__0;
                         switch($__19._tag_)
                          {case 0:
                            $__swJSW127__0=
                             $__9;
                            break;
                           case 1:
                            var $__20=
                             _e_($__16._2);
                            var $__swJSW128__0;
                            switch($__20._tag_)
                             {case 0:
                               var $__23=
                                _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,110,$__20._1]));
                               var $__swJSW129__0;
                               switch($__23._tag_)
                                {case 0:
                                  $__swJSW129__0=
                                   $__9;
                                  break;
                                 case 1:
                                  var $__24=
                                   _e_($__20._2);
                                  var $__swJSW130__0;
                                  switch($__24._tag_)
                                   {case 0:
                                     var $__27=
                                      _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,115,$__24._1]));
                                     var $__swJSW131__0;
                                     switch($__27._tag_)
                                      {case 0:
                                        $__swJSW131__0=
                                         $__9;
                                        break;
                                       case 1:
                                        var $__28=
                                         _e_($__24._2);
                                        var $__swJSW132__0;
                                        switch($__28._tag_)
                                         {case 0:
                                           $__swJSW132__0=
                                            $__9;
                                           break;
                                          case 1:
                                           var $__31=
                                            _e_($__);
                                           var $__swJSW133__0;
                                           switch($__31._tag_)
                                            {case 0:
                                              var $h34=
                                               new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$hNEW171UNQ597CCN,[$Show__,$__9,$__31._1,$__31._2]);
                                              var $h35=
                                               _e_($__31._1);
                                              var $__swJSW134__0;
                                              switch($h35._tag_)
                                               {case 0:
                                                 var $__38=
                                                  _e_($h35._1);
                                                 var $__swJSW135__0;
                                                 switch($__38._tag_)
                                                  {case 0:
                                                    var $__41=
                                                     _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,45,$__38._1]));
                                                    var $__swJSW136__0;
                                                    switch($__41._tag_)
                                                     {case 0:
                                                       var $__42=
                                                        _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,99,$__38._1]));
                                                       var $__swJSW137__0;
                                                       switch($__42._tag_)
                                                        {case 0:
                                                          $__swJSW137__0=
                                                           $h34;
                                                          break;
                                                         case 1:
                                                          var $__43=
                                                           _e_($__38._2);
                                                          var $__swJSW138__0;
                                                          switch($__43._tag_)
                                                           {case 0:
                                                             var $__46=
                                                              _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,111,$__43._1]));
                                                             var $__swJSW139__0;
                                                             switch($__46._tag_)
                                                              {case 0:
                                                                $__swJSW139__0=
                                                                 $h34;
                                                                break;
                                                               case 1:
                                                                var $__47=
                                                                 _e_($__43._2);
                                                                var $__swJSW140__0;
                                                                switch($__47._tag_)
                                                                 {case 0:
                                                                   var $__50=
                                                                    _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,110,$__47._1]));
                                                                   var $__swJSW141__0;
                                                                   switch($__50._tag_)
                                                                    {case 0:
                                                                      $__swJSW141__0=
                                                                       $h34;
                                                                      break;
                                                                     case 1:
                                                                      var $__51=
                                                                       _e_($__47._2);
                                                                      var $__swJSW142__0;
                                                                      switch($__51._tag_)
                                                                       {case 0:
                                                                         var $__54=
                                                                          _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,115,$__51._1]));
                                                                         var $__swJSW143__0;
                                                                         switch($__54._tag_)
                                                                          {case 0:
                                                                            $__swJSW143__0=
                                                                             $h34;
                                                                            break;
                                                                           case 1:
                                                                            var $__55=
                                                                             _e_($__51._2);
                                                                            var $__swJSW144__0;
                                                                            switch($__55._tag_)
                                                                             {case 0:
                                                                               $__swJSW144__0=
                                                                                $h34;
                                                                               break;
                                                                              case 1:
                                                                               var $__58=
                                                                                _e_($__31._2);
                                                                               var $__swJSW145__0;
                                                                               switch($__58._tag_)
                                                                                {case 0:
                                                                                  var $__61=
                                                                                   _e_($__58._2);
                                                                                  var $__swJSW146__0;
                                                                                  switch($__61._tag_)
                                                                                   {case 0:
                                                                                     $__swJSW146__0=
                                                                                      $h34;
                                                                                     break;
                                                                                    case 1:
                                                                                     var $__64=
                                                                                      new _A_($UHC.$Base.$show,[$Show__,$__58._1]);
                                                                                     var $__65=
                                                                                      new _A_($UHC.$Base.$packedStringToString,[":"]);
                                                                                     var $__66=
                                                                                      new _A_($UHC.$Base.$_2b_2b,[$__65,$__64]);
                                                                                     var $__67=
                                                                                      new _A_($UHC.$Base.$packedStringToString,[")"]);
                                                                                     var $__68=
                                                                                      new _A_($UHC.$Base.$_2b_2b,[$__67,$__66]);
                                                                                     var $__69=
                                                                                      new _A_($UHC.$Base.$show,[$Show__,$h35]);
                                                                                     var $__70=
                                                                                      new _A_($UHC.$Base.$_2b_2b,[$__69,$__68]);
                                                                                     var $__71=
                                                                                      new _A_($UHC.$Base.$packedStringToString,["("]);
                                                                                     var $__72=
                                                                                      new _A_($UHC.$Base.$_2b_2b,[$__71,$__70]);
                                                                                     $__swJSW146__0=
                                                                                      $__72;
                                                                                     break;}
                                                                                  $__swJSW145__0=
                                                                                   $__swJSW146__0;
                                                                                  break;
                                                                                 case 1:
                                                                                  $__swJSW145__0=
                                                                                   $h34;
                                                                                  break;}
                                                                               $__swJSW144__0=
                                                                                $__swJSW145__0;
                                                                               break;}
                                                                            $__swJSW143__0=
                                                                             $__swJSW144__0;
                                                                            break;}
                                                                         $__swJSW142__0=
                                                                          $__swJSW143__0;
                                                                         break;
                                                                        case 1:
                                                                         $__swJSW142__0=
                                                                          $h34;
                                                                         break;}
                                                                      $__swJSW141__0=
                                                                       $__swJSW142__0;
                                                                      break;}
                                                                   $__swJSW140__0=
                                                                    $__swJSW141__0;
                                                                   break;
                                                                  case 1:
                                                                   $__swJSW140__0=
                                                                    $h34;
                                                                   break;}
                                                                $__swJSW139__0=
                                                                 $__swJSW140__0;
                                                                break;}
                                                             $__swJSW138__0=
                                                              $__swJSW139__0;
                                                             break;
                                                            case 1:
                                                             $__swJSW138__0=
                                                              $h34;
                                                             break;}
                                                          $__swJSW137__0=
                                                           $__swJSW138__0;
                                                          break;}
                                                       $__swJSW136__0=
                                                        $__swJSW137__0;
                                                       break;
                                                      case 1:
                                                       var $__73=
                                                        _e_($__38._2);
                                                       var $__swJSW147__0;
                                                       switch($__73._tag_)
                                                        {case 0:
                                                          var $__76=
                                                           _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,62,$__73._1]));
                                                          var $__swJSW148__0;
                                                          switch($__76._tag_)
                                                           {case 0:
                                                             $__swJSW148__0=
                                                              $h34;
                                                             break;
                                                            case 1:
                                                             var $__77=
                                                              _e_($__73._2);
                                                             var $__swJSW149__0;
                                                             switch($__77._tag_)
                                                              {case 0:
                                                                $__swJSW149__0=
                                                                 $h34;
                                                                break;
                                                               case 1:
                                                                var $__80=
                                                                 _e_($__31._2);
                                                                var $__swJSW150__0;
                                                                switch($__80._tag_)
                                                                 {case 0:
                                                                   var $__83=
                                                                    _e_($__80._2);
                                                                   var $__swJSW151__0;
                                                                   switch($__83._tag_)
                                                                    {case 0:
                                                                      $__swJSW151__0=
                                                                       $h34;
                                                                      break;
                                                                     case 1:
                                                                      var $__86=
                                                                       new _A_($UHC.$Base.$show,[$Show__,$__80._1]);
                                                                      var $__87=
                                                                       new _A_($UHC.$Base.$packedStringToString,[":"]);
                                                                      var $__88=
                                                                       new _A_($UHC.$Base.$_2b_2b,[$__87,$__86]);
                                                                      var $__89=
                                                                       new _A_($UHC.$Base.$packedStringToString,[")"]);
                                                                      var $__90=
                                                                       new _A_($UHC.$Base.$_2b_2b,[$__89,$__88]);
                                                                      var $__91=
                                                                       new _A_($UHC.$Base.$show,[$Show__,$h35]);
                                                                      var $__92=
                                                                       new _A_($UHC.$Base.$_2b_2b,[$__91,$__90]);
                                                                      var $__93=
                                                                       new _A_($UHC.$Base.$packedStringToString,["("]);
                                                                      var $__94=
                                                                       new _A_($UHC.$Base.$_2b_2b,[$__93,$__92]);
                                                                      $__swJSW151__0=
                                                                       $__94;
                                                                      break;}
                                                                   $__swJSW150__0=
                                                                    $__swJSW151__0;
                                                                   break;
                                                                  case 1:
                                                                   $__swJSW150__0=
                                                                    $h34;
                                                                   break;}
                                                                $__swJSW149__0=
                                                                 $__swJSW150__0;
                                                                break;}
                                                             $__swJSW148__0=
                                                              $__swJSW149__0;
                                                             break;}
                                                          $__swJSW147__0=
                                                           $__swJSW148__0;
                                                          break;
                                                         case 1:
                                                          $__swJSW147__0=
                                                           $h34;
                                                          break;}
                                                       $__swJSW136__0=
                                                        $__swJSW147__0;
                                                       break;}
                                                    $__swJSW135__0=
                                                     $__swJSW136__0;
                                                    break;
                                                   case 1:
                                                    $__swJSW135__0=
                                                     $h34;
                                                    break;}
                                                 $__swJSW134__0=
                                                  $__swJSW135__0;
                                                 break;
                                                case 1:
                                                 $__swJSW134__0=
                                                  $h34;
                                                 break;}
                                              $__swJSW133__0=
                                               $__swJSW134__0;
                                              break;
                                             case 1:
                                              $__swJSW133__0=
                                               $__9;
                                              break;}
                                           $__swJSW132__0=
                                            $__swJSW133__0;
                                           break;}
                                        $__swJSW131__0=
                                         $__swJSW132__0;
                                        break;}
                                     $__swJSW130__0=
                                      $__swJSW131__0;
                                     break;
                                    case 1:
                                     $__swJSW130__0=
                                      $__9;
                                     break;}
                                  $__swJSW129__0=
                                   $__swJSW130__0;
                                  break;}
                               $__swJSW128__0=
                                $__swJSW129__0;
                               break;
                              case 1:
                               $__swJSW128__0=
                                $__9;
                               break;}
                            $__swJSW127__0=
                             $__swJSW128__0;
                            break;}
                         $__swJSW126__0=
                          $__swJSW127__0;
                         break;
                        case 1:
                         $__swJSW126__0=
                          $__9;
                         break;}
                      $__swJSW125__0=
                       $__swJSW126__0;
                      break;}
                   $__swJSW124__0=
                    $__swJSW125__0;
                   break;
                  case 1:
                   var $__96=
                    _e_($i10._2);
                   var $__swJSW152__0;
                   switch($__96._tag_)
                    {case 0:
                      var $__99=
                       _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,93,$__96._1]));
                      var $__swJSW153__0;
                      switch($__99._tag_)
                       {case 0:
                         $__swJSW153__0=
                          $__9;
                         break;
                        case 1:
                         var $__100=
                          _e_($__96._2);
                         var $__swJSW154__0;
                         switch($__100._tag_)
                          {case 0:
                            $__swJSW154__0=
                             $__9;
                            break;
                           case 1:
                            var $__103=
                             _e_($__);
                            var $__swJSW155__0;
                            switch($__103._tag_)
                             {case 0:
                               var $__106=
                                _e_($__103._2);
                               var $__swJSW156__0;
                               switch($__106._tag_)
                                {case 0:
                                  $__swJSW156__0=
                                   $__9;
                                  break;
                                 case 1:
                                  var $__109=
                                   new _A_($UHC.$Base.$packedStringToString,["]"]);
                                  var $__110=
                                   new _A_($UHC.$Base.$show,[$Show__,$__103._1]);
                                  var $__111=
                                   new _A_($UHC.$Base.$_2b_2b,[$__110,$__109]);
                                  var $__112=
                                   new _A_($UHC.$Base.$packedStringToString,["["]);
                                  var $__113=
                                   new _A_($UHC.$Base.$_2b_2b,[$__112,$__111]);
                                  $__swJSW156__0=
                                   $__113;
                                  break;}
                               $__swJSW155__0=
                                $__swJSW156__0;
                               break;
                              case 1:
                               $__swJSW155__0=
                                $__9;
                               break;}
                            $__swJSW154__0=
                             $__swJSW155__0;
                            break;}
                         $__swJSW153__0=
                          $__swJSW154__0;
                         break;}
                      $__swJSW152__0=
                       $__swJSW153__0;
                      break;
                     case 1:
                      $__swJSW152__0=
                       $__9;
                      break;}
                   $__swJSW124__0=
                    $__swJSW152__0;
                   break;}
                $__swJSW123__0=
                 $__swJSW124__0;
                break;
               case 1:
                var $__114=
                 _e_($i10._2);
                var $__swJSW157__0;
                switch($__114._tag_)
                 {case 0:
                   var $__117=
                    _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,62,$__114._1]));
                   var $__swJSW158__0;
                   switch($__117._tag_)
                    {case 0:
                      $__swJSW158__0=
                       $__9;
                      break;
                     case 1:
                      var $__118=
                       _e_($__114._2);
                      var $__swJSW159__0;
                      switch($__118._tag_)
                       {case 0:
                         $__swJSW159__0=
                          $__9;
                         break;
                        case 1:
                         var $__121=
                          _e_($__);
                         var $__swJSW160__0;
                         switch($__121._tag_)
                          {case 0:
                            var $f124=
                             new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$fNEW233UNQ676CCN,[$Show__,$__9,$__121._2,$__121._1]);
                            var $f125=
                             _e_($__121._1);
                            var $__swJSW161__0;
                            switch($f125._tag_)
                             {case 0:
                               var $__128=
                                _e_($f125._1);
                               var $__swJSW162__0;
                               switch($__128._tag_)
                                {case 0:
                                  var $__131=
                                   _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,45,$__128._1]));
                                  var $__swJSW163__0;
                                  switch($__131._tag_)
                                   {case 0:
                                     $__swJSW163__0=
                                      $f124;
                                     break;
                                    case 1:
                                     var $__132=
                                      _e_($__128._2);
                                     var $__swJSW164__0;
                                     switch($__132._tag_)
                                      {case 0:
                                        var $__135=
                                         _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,62,$__132._1]));
                                        var $__swJSW165__0;
                                        switch($__135._tag_)
                                         {case 0:
                                           $__swJSW165__0=
                                            $f124;
                                           break;
                                          case 1:
                                           var $__136=
                                            _e_($__132._2);
                                           var $__swJSW166__0;
                                           switch($__136._tag_)
                                            {case 0:
                                              $__swJSW166__0=
                                               $f124;
                                              break;
                                             case 1:
                                              var $__139=
                                               _e_($__121._2);
                                              var $__swJSW167__0;
                                              switch($__139._tag_)
                                               {case 0:
                                                 var $__142=
                                                  _e_($__139._2);
                                                 var $__swJSW168__0;
                                                 switch($__142._tag_)
                                                  {case 0:
                                                    $__swJSW168__0=
                                                     $f124;
                                                    break;
                                                   case 1:
                                                    var $__145=
                                                     new _A_($UHC.$Base.$show,[$Show__,$__139._1]);
                                                    var $__146=
                                                     new _A_($UHC.$Base.$packedStringToString,[" -> "]);
                                                    var $__147=
                                                     new _A_($UHC.$Base.$_2b_2b,[$__146,$__145]);
                                                    var $__148=
                                                     new _A_($UHC.$Base.$packedStringToString,[")"]);
                                                    var $__149=
                                                     new _A_($UHC.$Base.$_2b_2b,[$__148,$__147]);
                                                    var $__150=
                                                     new _A_($UHC.$Base.$show,[$Show__,$f125]);
                                                    var $__151=
                                                     new _A_($UHC.$Base.$_2b_2b,[$__150,$__149]);
                                                    var $__152=
                                                     new _A_($UHC.$Base.$packedStringToString,["("]);
                                                    var $__153=
                                                     new _A_($UHC.$Base.$_2b_2b,[$__152,$__151]);
                                                    $__swJSW168__0=
                                                     $__153;
                                                    break;}
                                                 $__swJSW167__0=
                                                  $__swJSW168__0;
                                                 break;
                                                case 1:
                                                 $__swJSW167__0=
                                                  $f124;
                                                 break;}
                                              $__swJSW166__0=
                                               $__swJSW167__0;
                                              break;}
                                           $__swJSW165__0=
                                            $__swJSW166__0;
                                           break;}
                                        $__swJSW164__0=
                                         $__swJSW165__0;
                                        break;
                                       case 1:
                                        $__swJSW164__0=
                                         $f124;
                                        break;}
                                     $__swJSW163__0=
                                      $__swJSW164__0;
                                     break;}
                                  $__swJSW162__0=
                                   $__swJSW163__0;
                                  break;
                                 case 1:
                                  $__swJSW162__0=
                                   $f124;
                                  break;}
                               $__swJSW161__0=
                                $__swJSW162__0;
                               break;
                              case 1:
                               $__swJSW161__0=
                                $f124;
                               break;}
                            $__swJSW160__0=
                             $__swJSW161__0;
                            break;
                           case 1:
                            $__swJSW160__0=
                             $__9;
                            break;}
                         $__swJSW159__0=
                          $__swJSW160__0;
                         break;}
                      $__swJSW158__0=
                       $__swJSW159__0;
                      break;}
                   $__swJSW157__0=
                    $__swJSW158__0;
                   break;
                  case 1:
                   $__swJSW157__0=
                    $__9;
                   break;}
                $__swJSW123__0=
                 $__swJSW157__0;
                break;}
             $__swJSW122__0=
              $__swJSW123__0;
             break;
            case 1:
             $__swJSW122__0=
              $__9;
             break;}
          return $__swJSW122__0;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$Show__DCT52__14__0DFLUHC_2eBase_2eshow=
 new _F_(function($Show__,$x1)
         {var $__=
           _e_($x1);
          var $__swJSW169__0;
          switch($__._tag_)
           {case 0:
             var $i6=
              new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$iNEW149UNQ569CCN,[$Show__,$__._1,$__._2]);
             var $__7=
              _e_($__._2);
             var $__swJSW170__0;
             switch($__7._tag_)
              {case 0:
                $__swJSW170__0=
                 $i6;
                break;
               case 1:
                $__swJSW170__0=
                 $__._1;
                break;}
             $__swJSW169__0=
              $__swJSW170__0;
             break;
            case 1:
             $__swJSW169__0=
              $__._1;
             break;}
          return $__swJSW169__0;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$Show__NEW265UNQ559EVLDCT52__14__0RDC=
 new _F_(function($Show__)
         {var $Show__2=
           _e_(new _A_($UHC.$Base.$Show__CLS74__43__0,[$Show__]));
          var $__6=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Show__DCT52__14__0DFLUHC_2eBase_2eshow,[$Show__]);
          var $__7=
           {_tag_:0,_1:$__6,_2:$Show__2._2,_3:$Show__2._3};
          return $__7;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$Show__NEW263UNQ520DCT52__14__0RDC=
 new _F_(function($Show__)
         {var $Show__2=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Show__NEW265UNQ559EVLDCT52__14__0RDC,[$Show__]);
          return $Show__2;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$Show__UNQ520DCT52__14__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Show__NEW263UNQ520DCT52__14__0RDC,[$Language.$Prolog.$NanoProlog.$NanoProlog.$Show__UNQ520DCT52__14__0RDC]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$Show__DCT52__14__0=
 new _A_(new _F_(function()
                 {return $Language.$Prolog.$NanoProlog.$NanoProlog.$Show__UNQ520DCT52__14__0RDC;}),[]);
$UHC.$Base.$_3e_3e=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._1;});
$Language.$UHC.$JS.$JQuery.$JQuery.$__removeClass_27=
 new _F_(function($__,$__2,$__3)
         {var $__4=
           _e_($__);
          var $__5=
           _e_($__2);
          var $__6=
           _e_($__4.removeClass($__5));
          var $__7=
           _e_([]);
          return [$__3,$__7];});
$Language.$UHC.$JS.$JQuery.$JQuery.$removeClass_27=
 new _F_(function($jq)
         {var $__=
           new _A_($Language.$UHC.$JS.$Types.$toJS,[$Language.$UHC.$JS.$ECMA.$String.$ToJS__DCT40__2__0]);
          var $__3=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$__removeClass_27,[$jq]);
          return new _A_($UHC.$Base.$_2e,[$__3,$__]);});
$JCU.$__44__5=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["blueField yellowField redField whiteField greenField"]);}),[]);
$JCU.$clearClasses=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$flip,[$Language.$UHC.$JS.$JQuery.$JQuery.$removeClass_27,$JCU.$__44__5]);}),[]);
$Language.$UHC.$JS.$JQuery.$JQuery.$__addClass=
 new _F_(function($__,$__2,$__3)
         {var $__4=
           _e_($__);
          var $__5=
           _e_($__2);
          var $__6=
           _e_($__4.addClass($__5));
          var $__7=
           _e_([]);
          return [$__3,$__7];});
$Language.$UHC.$JS.$JQuery.$JQuery.$addClass=
 new _F_(function($j,$s)
         {var $__=
           new _A_($Language.$UHC.$JS.$Types.$toJS,[$Language.$UHC.$JS.$ECMA.$String.$ToJS__DCT40__2__0,$s]);
          return new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$__addClass,[$j,$__]);});
$JCU.$markInvalidTerm=
 new _F_(function($jq)
         {var $__=
           new _A_($UHC.$Base.$packedStringToString,["blueField"]);
          var $__3=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$addClass,[$jq,$__]);
          var $__4=
           new _A_($JCU.$clearClasses,[$jq]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__4,$__3]);});
$Language.$UHC.$JS.$JQuery.$Droppable.$mkJSDroppable=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_(primToPlainObj($__3));
          return [$__2,$__4];});
$Language.$UHC.$JS.$JQuery.$Droppable.$__droppable=
 new _F_(function($__,$__2,$__3)
         {var $__4=
           _e_($__);
          var $__5=
           _e_($__2);
          var $__6=
           _e_($__4.droppable($__5));
          var $__7=
           _e_([]);
          return [$__3,$__7];});
$Language.$UHC.$JS.$JQuery.$Droppable.$_24okUNQ106=
 new _F_(function($jq,$_24x)
         {return new _A_($Language.$UHC.$JS.$JQuery.$Droppable.$__droppable,[$jq,$_24x]);});
$Language.$UHC.$JS.$JQuery.$Droppable.$droppable=
 new _F_(function($jq,$drop)
         {var $__=
           new _A_($Language.$UHC.$JS.$JQuery.$Droppable.$mkJSDroppable,[$drop]);
          var $__4=
           new _A_($Language.$UHC.$JS.$JQuery.$Droppable.$_24okUNQ106,[$jq]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__,$__4]);});
$UHC.$Base.$fail=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._3;});
$Prolog.$dummyProof=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          var $__5=
           new _A_($UHC.$Base.$map,[$Prolog.$dummyProof,$__2.subForest]);
          var $__6=
           new _A_($Data.$Tree.$Node__,[$Prolog.$Incomplete__,$__5]);
          return $__6;});
$Prolog.$Invalid__=
 new _A_(new _F_(function()
                 {return {_tag_:2};}),[]);
$Prolog.$mkNodeUNQ219=
 new _F_(function($x1,$x2,$cs,$st)
         {var $__=
           new _A_($UHC.$Base.$_2d,[$UHC.$Base.$Num__DCT74__101__0,$x1,1]);
          var $__6=
           new _A_($Prolog.$checkProof_27UNQ189,[$__,$x2]);
          var $__7=
           new _A_($UHC.$Base.$map,[$__6,$cs]);
          return new _A_($Data.$Tree.$Node__,[$st,$__7]);});
$Prolog.$isNothing=
 new _F_(function($x1)
         {var $__=
           _e_($x1);
          var $__swJSW175__0;
          switch($__._tag_)
           {case 0:
             $__swJSW175__0=
              $UHC.$Base.$False__;
             break;
            case 1:
             $__swJSW175__0=
              $UHC.$Base.$True__;
             break;}
          return $__swJSW175__0;});
$Prolog.$isJust=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_2e,[$UHC.$Base.$not,$Prolog.$isNothing]);}),[]);
$Data.$Map.$empty=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$_5b_5d;}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$emptyEnv=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Just__,[$Data.$Map.$empty]);}),[]);
$UHC.$Base.$foldl_27=
 new _F_(function($x1,$x2,$x3)
         {var $x34=
           _e_($x3);
          var $__swJSW176__0;
          switch($x34._tag_)
           {case 0:
             var $fax=
              new _A_($x1,[$x2,$x34._1]);
             var $fax8=
              _e_($fax);
             $__swJSW176__0=
              new _A_($UHC.$Base.$foldl_27,[$x1,$fax,$x34._2]);
             break;
            case 1:
             $__swJSW176__0=
              $x2;
             break;}
          return $__swJSW176__0;});
$UHC.$Base.$__78__11901__0=
 new _F_(function($n,$__)
         {return new _A_($UHC.$Base.$_2b,[$UHC.$Base.$Num__DCT74__101__0,$n,1]);});
$UHC.$Base.$length=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$foldl_27,[$UHC.$Base.$__78__11901__0,0]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$Env__=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$id;}),[]);
$Data.$Map.$insert=
 new _F_(function($k,$v)
         {var $__=
           [$k,$v];
          return new _A_($UHC.$Base.$_3a,[$__]);});
$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__1935__0NEW634UNQ469CCN=
 new _F_(function($x1,$x2)
         {var $x13=
           _e_($x1);
          var $x26=
           _e_($x2);
          var $__swJSW178__0;
          switch($x26._tag_)
           {case 0:
             var $__=
              new _A_($UHC.$Base.$Eq__DCT74__394__0,[$UHC.$Base.$Eq__DCT74__56__0]);
             var $__9=
              new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$subst,[$Language.$Prolog.$NanoProlog.$NanoProlog.$Subst__DCT52__10__0,$x26._1,$x13[0]]);
             $__swJSW178__0=
              new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$matchUNQ487,[$x26,$x26._1,$__,$__9,$x13[1]]);
             break;
            case 1:
             $__swJSW178__0=
              $UHC.$Base.$undefined;
             break;}
          return $__swJSW178__0;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$matchUNQ487=
 new _F_(function($x2,$e,$__,$x1,$x25)
         {var $x16=
           _e_($x1);
          var $__swJSW179__0;
          switch($x16._tag_)
           {case 0:
             var $x29=
              _e_($x25);
             var $__swJSW180__0;
             switch($x29._tag_)
              {case 0:
                var $__12=
                 new _A_($UHC.$Base.$length,[$x29._2]);
                var $__13=
                 new _A_($UHC.$Base.$length,[$x16._2]);
                var $__14=
                 new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__88__0,$__13,$__12]);
                var $__15=
                 new _A_($UHC.$Base.$_3d_3d,[$__,$x16._1,$x29._1]);
                var $__16=
                 new _A_($UHC.$Base.$_26_26,[$__15,$__14]);
                var $__17=
                 _e_($__16);
                var $__swJSW181__0;
                switch($__17._tag_)
                 {case 0:
                   $__swJSW181__0=
                    $UHC.$Base.$Nothing__;
                   break;
                  case 1:
                   var $__18=
                    new _A_($UHC.$Base.$zip,[$x16._2,$x29._2]);
                   var $__19=
                    new _A_($UHC.$Base.$foldr,[$Language.$Prolog.$NanoProlog.$NanoProlog.$matches,$x2,$__18]);
                   $__swJSW181__0=
                    $__19;
                   break;}
                $__swJSW180__0=
                 $__swJSW181__0;
                break;
               case 1:
                $__swJSW180__0=
                 $UHC.$Base.$Nothing__;
                break;}
             $__swJSW179__0=
              $__swJSW180__0;
             break;
            case 1:
             var $__22=
              new _A_($Data.$Map.$insert,[$x16._1,$x25,$e]);
             var $__23=
              new _A_($UHC.$Base.$_2e,[$UHC.$Base.$Just__,$Language.$Prolog.$NanoProlog.$NanoProlog.$Env__]);
             var $__24=
              new _A_($UHC.$Base.$_24,[$__23,$__22]);
             $__swJSW179__0=
              $__24;
             break;}
          return $__swJSW179__0;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$matches=
 new _F_(function($x1,$x2)
         {var $__=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$__54__1935__0NEW634UNQ469CCN,[$x1,$x2]);
          var $x24=
           _e_($x2);
          var $__swJSW182__0;
          switch($x24._tag_)
           {case 0:
             $__swJSW182__0=
              $__;
             break;
            case 1:
             $__swJSW182__0=
              $UHC.$Base.$Nothing__;
             break;}
          return $__swJSW182__0;});
$Prolog.$tryRule=
 new _F_(function($tm,$cs,$__)
         {var $__4=
           _e_($__);
          var $__7=
           [$__4._1,$tm];
          var $__8=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$matches,[$__7,$Language.$Prolog.$NanoProlog.$NanoProlog.$emptyEnv]);
          var $__9=
           new _A_($UHC.$Base.$zip,[$__4._2,$cs]);
          var $__10=
           new _A_($UHC.$Base.$foldr,[$Language.$Prolog.$NanoProlog.$NanoProlog.$matches,$__8,$__9]);
          var $__11=
           new _A_($Prolog.$isJust,[$__10]);
          var $__12=
           new _A_($UHC.$Base.$length,[$__4._2]);
          var $__13=
           new _A_($UHC.$Base.$length,[$cs]);
          var $__14=
           new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__88__0,$__13,$__12]);
          var $__15=
           new _A_($UHC.$Base.$_26_26,[$__14,$__11]);
          var $__16=
           _e_($__8);
          var $__swJSW184__0;
          switch($__16._tag_)
           {case 0:
             $__swJSW184__0=
              $__15;
             break;
            case 1:
             $__swJSW184__0=
              $UHC.$Base.$False__;
             break;}
          return $__swJSW184__0;});
$Prolog.$Incomplete__=
 new _A_(new _F_(function()
                 {return {_tag_:1};}),[]);
$Data.$Tree.$rootLabel=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return $__2.rootLabel;});
$Prolog.$hasVars=
 new _F_(function($x1)
         {var $__=
           _e_($x1);
          var $__swJSW186__0;
          switch($__._tag_)
           {case 0:
             var $__5=
              new _A_($UHC.$Base.$any,[$Prolog.$hasVars,$__._2]);
             var $__6=
              _e_($__._2);
             var $__swJSW187__0;
             switch($__6._tag_)
              {case 0:
                $__swJSW187__0=
                 $__5;
                break;
               case 1:
                $__swJSW187__0=
                 $UHC.$Base.$False__;
                break;}
             $__swJSW186__0=
              $__swJSW187__0;
             break;
            case 1:
             $__swJSW186__0=
              $UHC.$Base.$True__;
             break;}
          return $__swJSW186__0;});
$Prolog.$nNEW644UNQ208CCN=
 new _F_(function($x1,$x2,$x3)
         {var $x34=
           _e_($x3);
          var $__=
           new _A_($UHC.$Base.$map,[$Data.$Tree.$rootLabel,$x34.subForest]);
          var $__8=
           new _A_($Prolog.$tryRule,[$x34.rootLabel,$__]);
          var $rlsMatch=
           new _A_($UHC.$Base.$any,[$__8,$x2]);
          var $__10=
           _e_($rlsMatch);
          var $__swJSW189__0;
          switch($__10._tag_)
           {case 0:
             var $__11=
              _e_($UHC.$Base.$otherwise);
             var $__swJSW190__0;
             switch($__11._tag_)
              {case 0:
                $__swJSW190__0=
                 $UHC.$Base.$undefined;
                break;
               case 1:
                var $__12=
                 new _A_($UHC.$Base.$null,[$x34.subForest]);
                var $__13=
                 _e_($__12);
                var $__swJSW191__0;
                switch($__13._tag_)
                 {case 0:
                   var $__14=
                    new _A_($Prolog.$mkNodeUNQ219,[$x1,$x2,$x34.subForest,$Prolog.$Invalid__]);
                   $__swJSW191__0=
                    $__14;
                   break;
                  case 1:
                   var $__15=
                    new _A_($Prolog.$mkNodeUNQ219,[$x1,$x2,$x34.subForest,$Prolog.$Incomplete__]);
                   $__swJSW191__0=
                    $__15;
                   break;}
                $__swJSW190__0=
                 $__swJSW191__0;
                break;}
             $__swJSW189__0=
              $__swJSW190__0;
             break;
            case 1:
             var $__16=
              new _A_($Prolog.$hasVars,[$x34.rootLabel]);
             var $__17=
              _e_($__16);
             var $__swJSW192__0;
             switch($__17._tag_)
              {case 0:
                var $__18=
                 new _A_($Prolog.$mkNodeUNQ219,[$x1,$x2,$x34.subForest,$Prolog.$Correct__]);
                $__swJSW192__0=
                 $__18;
                break;
               case 1:
                var $__19=
                 new _A_($Prolog.$mkNodeUNQ219,[$x1,$x2,$x34.subForest,$Prolog.$Incomplete__]);
                $__swJSW192__0=
                 $__19;
                break;}
             $__swJSW189__0=
              $__swJSW192__0;
             break;}
          return $__swJSW189__0;});
$Prolog.$checkProof_27UNQ189=
 new _F_(function($x1,$x2,$x3)
         {var $n=
           new _A_($Prolog.$nNEW644UNQ208CCN,[$x1,$x2,$x3]);
          var $__=
           new _A_($UHC.$Base.$_3c_3d,[$UHC.$Base.$Ord__DCT74__91__0,$x1,0]);
          var $__6=
           _e_($__);
          var $__swJSW193__0;
          switch($__6._tag_)
           {case 0:
             $__swJSW193__0=
              $n;
             break;
            case 1:
             var $__7=
              new _A_($UHC.$Base.$packedStringToString,["Proof checking depth reached."]);
             var $__8=
              new _A_($UHC.$Base.$error,[$__7]);
             $__swJSW193__0=
              $__8;
             break;}
          return $__swJSW193__0;});
$Prolog.$checkProof=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$checkProof_27UNQ189,[100]);}),[]);
$JCU.$__44__136NEW58=
 new _F_(function($p,$_24x,$_24x3)
         {var $__=
           _e_($_24x3);
          var $__swJSW194__0;
          switch($__._tag_)
           {case 0:
             var $__5=
              new _A_($Prolog.$dummyProof,[$p]);
             $__swJSW194__0=
              $__5;
             break;
            case 1:
             var $__6=
              new _A_($Prolog.$checkProof,[$_24x,$p]);
             $__swJSW194__0=
              $__6;
             break;}
          return $__swJSW194__0;});
$JCU.$_24okUNQ196=
 new _F_(function($p,$_24x,$_24x3)
         {var $__=
           new _A_($JCU.$__44__136NEW58,[$p,$_24x,$_24x3]);
          var $__5=
           new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0]);
          return new _A_($UHC.$Base.$_24,[$__5,$__]);});
$JCU.$_24okUNQ192=
 new _F_(function($p,$_24x)
         {var $__=
           new _A_($Data.$LocalStorage.$getLocalStorage,[$UHC.$Base.$__74__51__0,$JCU.$checkProofStoreKey]);
          var $__4=
           new _A_($JCU.$_24okUNQ196,[$p,$_24x]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__,$__4]);});
$Models.$Read__DCT82__6__0DFLUHC_2eBase_2ereadsPrec=
 new _F_(function($__,$str)
         {var $__3=
           new _A_($Language.$Prolog.$NanoProlog.$ParserUUTC.$startParse,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$pRule,$str]);
          var $__4=
           new _A_($UHC.$Base.$_2e,[$UHC.$Base.$null,$UHC.$Base.$snd]);
          var $__5=
           new _A_($Data.$List.$find,[$__4]);
          var $__6=
           new _A_($UHC.$Base.$_24,[$__5,$__3]);
          var $__7=
           _e_($__6);
          var $__swJSW195__0;
          switch($__7._tag_)
           {case 0:
             var $__9=
              new _A_($UHC.$Base.$_3a,[$__7._1,$UHC.$Base.$_5b_5d]);
             $__swJSW195__0=
              $__9;
             break;
            case 1:
             $__swJSW195__0=
              $UHC.$Base.$_5b_5d;
             break;}
          return $__swJSW195__0;});
$Models.$__86__401=
 new _A_(new _F_(function()
                 {return new _A_($ParseLib.$Abstract.$Core.$succeed,[$UHC.$Base.$_5b_5d]);}),[]);
$ParseLib.$Abstract.$Applications.$commaList=
 new _F_(function($p)
         {var $__=
           new _A_($ParseLib.$Abstract.$Derived.$symbol,[$UHC.$Base.$Eq__DCT74__56__0,44]);
          return new _A_($ParseLib.$Abstract.$Derived.$listOf,[$p,$__]);});
$Models.$__86__400=
 new _A_(new _F_(function()
                 {return new _A_($ParseLib.$Abstract.$Applications.$commaList,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$pRule]);}),[]);
$Models.$__86__397=
 new _A_(new _F_(function()
                 {return new _A_($Control.$Applicative.$_3c_7c_3e,[$ParseLib.$Abstract.$Core.$Alternative__DCT142__2__0,$Models.$__86__400,$Models.$__86__401]);}),[]);
$Models.$pRules=
 new _A_(new _F_(function()
                 {return new _A_($ParseLib.$Abstract.$Applications.$bracketed,[$Models.$__86__397]);}),[]);
$Models.$Read__DCT82__6__0DFLUHC_2eBase_2ereadList=
 new _F_(function($str)
         {var $__=
           new _A_($Language.$Prolog.$NanoProlog.$ParserUUTC.$startParse,[$Models.$pRules,$str]);
          var $__3=
           new _A_($UHC.$Base.$_2e,[$UHC.$Base.$null,$UHC.$Base.$snd]);
          var $__4=
           new _A_($Data.$List.$find,[$__3]);
          var $__5=
           new _A_($UHC.$Base.$_24,[$__4,$__]);
          var $__6=
           _e_($__5);
          var $__swJSW196__0;
          switch($__6._tag_)
           {case 0:
             var $__8=
              new _A_($UHC.$Base.$_3a,[$__6._1,$UHC.$Base.$_5b_5d]);
             $__swJSW196__0=
              $__8;
             break;
            case 1:
             $__swJSW196__0=
              $UHC.$Base.$_5b_5d;
             break;}
          return $__swJSW196__0;});
$Models.$Read__NEW234UNQ272EVLDCT82__6__0RDC=
 new _F_(function($Read__)
         {var $Read__2=
           _e_(new _A_($UHC.$Base.$Read__CLS74__41__0,[$Read__]));
          var $__5=
           {_tag_:0,_1:$Models.$Read__DCT82__6__0DFLUHC_2eBase_2ereadList,_2:$Models.$Read__DCT82__6__0DFLUHC_2eBase_2ereadsPrec};
          return $__5;});
$Models.$Read__NEW232UNQ271DCT82__6__0RDC=
 new _F_(function($Read__)
         {var $Read__2=
           new _A_($Models.$Read__NEW234UNQ272EVLDCT82__6__0RDC,[$Read__]);
          return $Read__2;});
$Models.$Read__UNQ271DCT82__6__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($Models.$Read__NEW232UNQ271DCT82__6__0RDC,[$Models.$Read__UNQ271DCT82__6__0RDC]);}),[]);
$Models.$Read__DCT82__6__0=
 new _A_(new _F_(function()
                 {return $Models.$Read__UNQ271DCT82__6__0RDC;}),[]);
$UHC.$Base.$readList=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._1;});
$UHC.$Base.$Read__DCT74__86__0DFLUHC_2eBase_2ereadsPrec=
 new _F_(function($__,$p)
         {return new _A_($UHC.$Base.$readList,[$__]);});
$UHC.$Base.$Read__NEW5225UNQ11593EVLDCT74__86__0RDC=
 new _F_(function($__,$Read__)
         {var $Read__3=
           _e_(new _A_($UHC.$Base.$Read__CLS74__41__0,[$Read__]));
          var $__6=
           new _A_($UHC.$Base.$Read__DCT74__86__0DFLUHC_2eBase_2ereadsPrec,[$__]);
          var $__7=
           {_tag_:0,_1:$Read__3._1,_2:$__6};
          return $__7;});
$UHC.$Base.$Read__NEW5222UNQ11591DCT74__86__0RDC=
 new _F_(function($__,$Read__)
         {var $Read__3=
           new _A_($UHC.$Base.$Read__NEW5225UNQ11593EVLDCT74__86__0RDC,[$__,$Read__]);
          return $Read__3;});
$UHC.$Base.$Read__DCT74__86__0=
 new _F_(function($__)
         {var $Read__=
           _i_();
          _i_set_($Read__,new _A_($UHC.$Base.$Read__NEW5222UNQ11591DCT74__86__0RDC,[$__,$Read__]));
          return $Read__;});
$JCU.$__42__1421__2__0=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Read__DCT74__86__0,[$Models.$Read__DCT82__6__0]);}),[]);
$JCU.$rulesStoreKey=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["rules"]);}),[]);
$JCU.$readRulesFromStore=
 new _A_(new _F_(function()
                 {return new _A_($Data.$LocalStorage.$getLocalStorage,[$JCU.$__42__1421__2__0,$JCU.$rulesStoreKey]);}),[]);
$JCU.$checkProof=
 new _F_(function($p)
         {var $__=
           new _A_($JCU.$_24okUNQ192,[$p]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$JCU.$readRulesFromStore,$__]);});
$Language.$UHC.$JS.$JQuery.$JQuery.$__append=
 new _F_(function($__,$__2,$__3)
         {var $__4=
           _e_($__);
          var $__5=
           _e_($__2);
          var $__6=
           _e_($__4.append($__5));
          var $__7=
           _e_([]);
          return [$__3,$__7];});
$Language.$UHC.$JS.$JQuery.$JQuery.$_24okUNQ888=
 new _F_(function($jq,$_24x)
         {return new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$__append,[$jq,$_24x]);});
$Language.$UHC.$JS.$JQuery.$JQuery.$appendString=
 new _F_(function($jq,$str)
         {var $__=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$jQuery,[$str]);
          var $__4=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$_24okUNQ888,[$jq]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__,$__4]);});
$Data.$List.$intersperse=
 new _F_(function($x1,$x2)
         {var $x23=
           _e_($x2);
          var $__swJSW200__0;
          switch($x23._tag_)
           {case 0:
             var $__6=
              new _A_($Data.$List.$intersperse,[$x1,$x23._2]);
             var $__7=
              new _A_($UHC.$Base.$_3a,[$x1,$__6]);
             var $__8=
              new _A_($UHC.$Base.$_3a,[$x23._1,$__7]);
             var $__9=
              _e_($x23._2);
             var $__swJSW201__0;
             switch($__9._tag_)
              {case 0:
                $__swJSW201__0=
                 $__8;
                break;
               case 1:
                var $__12=
                 new _A_($UHC.$Base.$_3a,[$x23._1,$UHC.$Base.$_5b_5d]);
                $__swJSW201__0=
                 $__12;
                break;}
             $__swJSW200__0=
              $__swJSW201__0;
             break;
            case 1:
             $__swJSW200__0=
              $UHC.$Base.$_5b_5d;
             break;}
          return $__swJSW200__0;});
$Data.$List.$intercalate=
 new _F_(function($xs,$xss)
         {var $__=
           new _A_($Data.$List.$intersperse,[$xs,$xss]);
          return new _A_($UHC.$Base.$concat,[$__]);});
$Models.$tryParseTerm=
 new _A_(new _F_(function()
                 {return new _A_($Models.$run,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$pTerm]);}),[]);
$JCU.$ruleTreeId=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["ul#proof-tree-view.tree"]);}),[]);
$Language.$UHC.$JS.$JQuery.$JQuery.$Click__=
 new _A_(new _F_(function()
                 {return {_tag_:2};}),[]);
$Data.$LocalStorage.$__setLocalStorage=
 new _F_(function($__,$__2,$__3)
         {var $__4=
           _e_($__);
          var $__5=
           _e_($__2);
          var $__6=
           _e_(localStorage.setItem($__4,$__5));
          var $__7=
           _e_([]);
          return [$__3,$__7];});
$Data.$LocalStorage.$setLocalStorage=
 new _F_(function($__,$key)
         {var $__3=
           new _A_($UHC.$Base.$show,[$__]);
          var $__4=
           new _A_($Language.$UHC.$JS.$Types.$toJS,[$Language.$UHC.$JS.$ECMA.$String.$ToJS__DCT40__2__0]);
          var $__5=
           new _A_($UHC.$Base.$_2e,[$__4,$__3]);
          var $__6=
           new _A_($Language.$UHC.$JS.$Types.$toJS,[$Language.$UHC.$JS.$ECMA.$String.$ToJS__DCT40__2__0,$key]);
          var $__7=
           new _A_($Data.$LocalStorage.$__setLocalStorage,[$__6]);
          return new _A_($UHC.$Base.$_2e,[$__7,$__5]);});
$Data.$LocalStorage.$_24okUNQ234=
 new _F_(function($__,$key,$f,$_24x)
         {var $__5=
           new _A_($f,[$_24x]);
          return new _A_($Data.$LocalStorage.$setLocalStorage,[$__,$key,$__5]);});
$UHC.$Base.$_24okUNQ8788=
 new _F_(function($x,$_24x)
         {var $__=
           _e_($_24x);
          var $__6=
           _e_($__[0]);
          var $__swJSW203__0;
          switch($__6._tag_)
           {case 0:
             $__swJSW203__0=
              $UHC.$Base.$_5b_5d;
             break;
            case 1:
             var $__9=
              _e_($__[1]);
             var $__swJSW204__0;
             switch($__9._tag_)
              {case 0:
                $__swJSW204__0=
                 $UHC.$Base.$_5b_5d;
                break;
               case 1:
                var $__12=
                 new _A_($UHC.$Base.$_3a,[$x,$UHC.$Base.$_5b_5d]);
                $__swJSW204__0=
                 $__12;
                break;}
             $__swJSW203__0=
              $__swJSW204__0;
             break;}
          return $__swJSW203__0;});
$UHC.$Base.$_24okUNQ8775=
 new _F_(function($_24x)
         {var $__=
           _e_($_24x);
          var $__5=
           new _A_($UHC.$Base.$lex,[$__[1]]);
          var $__6=
           new _A_($UHC.$Base.$_24okUNQ8788,[$__[0]]);
          return new _A_($UHC.$Base.$concatMap,[$__6,$__5]);});
$UHC.$Base.$__76__40235__0NEW5286UNQ8774=
 new _F_(function($__,$s)
         {var $__3=
           new _A_($UHC.$Base.$reads,[$__,$s]);
          return new _A_($UHC.$Base.$concatMap,[$UHC.$Base.$_24okUNQ8775,$__3]);});
$UHC.$Base.$read=
 new _F_(function($__,$s)
         {var $__3=
           new _A_($UHC.$Base.$__76__40235__0NEW5286UNQ8774,[$__,$s]);
          var $__4=
           new _A_($UHC.$Base.$packedStringToString,["Prelude.read: ambiguous parse"]);
          var $__5=
           new _A_($UHC.$Base.$error,[$__4]);
          var $__6=
           _e_($__3);
          var $__swJSW206__0;
          switch($__6._tag_)
           {case 0:
             var $__9=
              _e_($__6._2);
             var $__swJSW207__0;
             switch($__9._tag_)
              {case 0:
                $__swJSW207__0=
                 $__5;
                break;
               case 1:
                $__swJSW207__0=
                 $__6._1;
                break;}
             $__swJSW206__0=
              $__swJSW207__0;
             break;
            case 1:
             var $__12=
              new _A_($UHC.$Base.$packedStringToString,["Prelude.read: no parse"]);
             var $__13=
              new _A_($UHC.$Base.$error,[$__12]);
             $__swJSW206__0=
              $__13;
             break;}
          return $__swJSW206__0;});
$Data.$LocalStorage.$__getLocalStorage=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_(localStorage.getItem($__3));
          return [$__2,$__4];});
$Data.$LocalStorage.$getLocalStorage=
 new _F_(function($__)
         {var $__2=
           new _A_($Language.$UHC.$JS.$Types.$toJS,[$Language.$UHC.$JS.$ECMA.$String.$ToJS__DCT40__2__0]);
          var $__3=
           new _A_($UHC.$Base.$_2e,[$Data.$LocalStorage.$__getLocalStorage,$__2]);
          var $__4=
           new _A_($Language.$UHC.$JS.$Types.$fromJS,[$Language.$UHC.$JS.$ECMA.$String.$FromJS__DCT40__4__0]);
          var $__5=
           new _A_($UHC.$Base.$read,[$__]);
          var $__6=
           new _A_($UHC.$Base.$_2e,[$__5,$__4]);
          var $__7=
           new _A_($UHC.$Base.$fmap,[$UHC.$Base.$Functor__DCT74__338__0,$__6]);
          return new _A_($UHC.$Base.$_2e,[$__7,$__3]);});
$Data.$LocalStorage.$modifyLocalStorage=
 new _F_(function($__,$__2,$key,$f)
         {var $__5=
           new _A_($Data.$LocalStorage.$getLocalStorage,[$__,$key]);
          var $__6=
           new _A_($Data.$LocalStorage.$_24okUNQ234,[$__2,$key,$f]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__5,$__6]);});
$UHC.$Base.$Functor__NEW3733UNQ10314EVLDCT74__404__0RDC=
 new _F_(function($Functor__,$Functor__2)
         {var $Functor__3=
           _e_(new _A_($UHC.$Base.$Functor__CLS74__44__0,[$Functor__2]));
          var $__5=
           {_tag_:0,_1:$Functor__};
          return $__5;});
$UHC.$Base.$Functor__NEW3730UNQ10305DCT74__404__0RDC=
 new _F_(function($Functor__,$Functor__2)
         {var $Functor__3=
           new _A_($UHC.$Base.$Functor__NEW3733UNQ10314EVLDCT74__404__0RDC,[$Functor__,$Functor__2]);
          return $Functor__3;});
$UHC.$Base.$Par1__=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$id;}),[]);
$UHC.$Base.$__Rep1MaybeDFLUHC_2eBase_2efrom1GENRepresentable1=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          var $__swJSW209__0;
          switch($x2._tag_)
           {case 0:
             var $__4=
              new _A_($UHC.$Base.$Par1__,[$x2._1]);
             var $__5=
              new _A_($UHC.$Base.$M1__,[$__4]);
             var $__6=
              new _A_($UHC.$Base.$M1__,[$__5]);
             var $__7=
              new _A_($UHC.$Base.$R1__,[$__6]);
             var $__8=
              new _A_($UHC.$Base.$M1__,[$__7]);
             $__swJSW209__0=
              $__8;
             break;
            case 1:
             var $__=
              new _A_($UHC.$Base.$M1__,[$UHC.$Base.$U1__]);
             var $__10=
              new _A_($UHC.$Base.$L1__,[$__]);
             var $__11=
              new _A_($UHC.$Base.$M1__,[$__10]);
             $__swJSW209__0=
              $__11;
             break;}
          return $__swJSW209__0;});
$UHC.$Base.$__Rep1MaybeDFLUHC_2eBase_2eto1GENRepresentable1=
 new _F_(function($proj__1)
         {var $proj__2=
           _e_($proj__1);
          var $__swJSW210__0;
          switch($proj__2._tag_)
           {case 0:
             var $proj__4=
              _e_($proj__2.unL1);
             $__swJSW210__0=
              $UHC.$Base.$Nothing__;
             break;
            case 1:
             var $__=
              new _A_($UHC.$Base.$Just__,[$proj__2.unR1]);
             $__swJSW210__0=
              $__;
             break;}
          return $__swJSW210__0;});
$UHC.$Base.$Representable1__CLS74__370__0=
 new _F_(function($Representable1__)
         {var $Representable1__2=
           {_tag_:0,_1:$UHC.$Base.$undefined,_2:$UHC.$Base.$undefined};
          return $Representable1__2;});
$UHC.$Base.$__Rep1MaybeNEW3719UNQ1721EVLSDCGENRepresentable1=
 new _F_(function($__)
         {var $Representable1__=
           _e_(new _A_($UHC.$Base.$Representable1__CLS74__370__0,[$__]));
          var $__5=
           {_tag_:0,_1:$UHC.$Base.$__Rep1MaybeDFLUHC_2eBase_2efrom1GENRepresentable1,_2:$UHC.$Base.$__Rep1MaybeDFLUHC_2eBase_2eto1GENRepresentable1};
          return $__5;});
$UHC.$Base.$__Rep1MaybeNEW3717UNQ1720SDCGENRepresentable1=
 new _F_(function($__)
         {var $__2=
           new _A_($UHC.$Base.$__Rep1MaybeNEW3719UNQ1721EVLSDCGENRepresentable1,[$__]);
          return $__2;});
$UHC.$Base.$__Rep1MaybeUNQ1720SDCGENRepresentable1=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$__Rep1MaybeNEW3717UNQ1720SDCGENRepresentable1,[$UHC.$Base.$__Rep1MaybeUNQ1720SDCGENRepresentable1]);}),[]);
$UHC.$Base.$__Rep1MaybeGENRepresentable1=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$__Rep1MaybeUNQ1720SDCGENRepresentable1;}),[]);
$UHC.$Base.$from1=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._1;});
$UHC.$Base.$to1=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._2;});
$UHC.$Base.$asTypeOf=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$const;}),[]);
$UHC.$Base.$fmapDefault=
 new _F_(function($__,$__2,$ra,$f,$x)
         {var $__6=
           new _A_($UHC.$Base.$from1,[$__,$x]);
          var $__7=
           new _A_($UHC.$Base.$asTypeOf,[$__6,$ra]);
          var $__8=
           new _A_($UHC.$Base.$fmap_27,[$__2,$f,$__7]);
          return new _A_($UHC.$Base.$to1,[$__,$__8]);});
$UHC.$Base.$Functor_27__DCT74__396__0DFLUHC_2eBase_2efmap_27=
 new _F_(function($f,$__)
         {var $__3=
           _e_($__);
          return $UHC.$Base.$U1__;});
$UHC.$Base.$Functor_27__NEW701UNQ10329EVLDCT74__396__0RDC=
 new _F_(function($Functor_27__)
         {var $Functor_27__2=
           _e_(new _A_($UHC.$Base.$Functor_27__CLS74__395__0,[$Functor_27__]));
          var $__4=
           {_tag_:0,_1:$UHC.$Base.$Functor_27__DCT74__396__0DFLUHC_2eBase_2efmap_27};
          return $__4;});
$UHC.$Base.$Functor_27__NEW699UNQ10328DCT74__396__0RDC=
 new _F_(function($Functor_27__)
         {var $Functor_27__2=
           new _A_($UHC.$Base.$Functor_27__NEW701UNQ10329EVLDCT74__396__0RDC,[$Functor_27__]);
          return $Functor_27__2;});
$UHC.$Base.$Functor_27__UNQ10328DCT74__396__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Functor_27__NEW699UNQ10328DCT74__396__0RDC,[$UHC.$Base.$Functor_27__UNQ10328DCT74__396__0RDC]);}),[]);
$UHC.$Base.$Functor_27__DCT74__396__0=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$Functor_27__UNQ10328DCT74__396__0RDC;}),[]);
$UHC.$Base.$__76__44143__2__3UNQ10311=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Functor_27__DCT74__400__0,[$UHC.$Base.$Functor_27__DCT74__396__0]);}),[]);
$UHC.$Base.$Functor_27__DCT74__397__0DFLUHC_2eBase_2efmap_27=
 new _F_(function($f,$__)
         {return new _A_($f,[$__]);});
$UHC.$Base.$Functor_27__NEW709UNQ10336EVLDCT74__397__0RDC=
 new _F_(function($Functor_27__)
         {var $Functor_27__2=
           _e_(new _A_($UHC.$Base.$Functor_27__CLS74__395__0,[$Functor_27__]));
          var $__4=
           {_tag_:0,_1:$UHC.$Base.$Functor_27__DCT74__397__0DFLUHC_2eBase_2efmap_27};
          return $__4;});
$UHC.$Base.$Functor_27__NEW707UNQ10335DCT74__397__0RDC=
 new _F_(function($Functor_27__)
         {var $Functor_27__2=
           new _A_($UHC.$Base.$Functor_27__NEW709UNQ10336EVLDCT74__397__0RDC,[$Functor_27__]);
          return $Functor_27__2;});
$UHC.$Base.$Functor_27__UNQ10335DCT74__397__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Functor_27__NEW707UNQ10335DCT74__397__0RDC,[$UHC.$Base.$Functor_27__UNQ10335DCT74__397__0RDC]);}),[]);
$UHC.$Base.$Functor_27__DCT74__397__0=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$Functor_27__UNQ10335DCT74__397__0RDC;}),[]);
$UHC.$Base.$__76__44143__2__6UNQ10307=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Functor_27__DCT74__400__0,[$UHC.$Base.$Functor_27__DCT74__397__0]);}),[]);
$UHC.$Base.$__76__44143__2__5UNQ10306=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Functor_27__DCT74__400__0,[$UHC.$Base.$__76__44143__2__6UNQ10307]);}),[]);
$UHC.$Base.$Functor_27__DCT74__401__0DFLUHC_2eBase_2efmap_27=
 new _F_(function($__,$__2,$x1,$x2)
         {var $x25=
           _e_($x2);
          var $__swJSW218__0;
          switch($x25._tag_)
           {case 0:
             var $__7=
              new _A_($UHC.$Base.$fmap_27,[$__,$x1,$x25.unL1]);
             var $__8=
              new _A_($UHC.$Base.$L1__,[$__7]);
             $__swJSW218__0=
              $__8;
             break;
            case 1:
             var $__10=
              new _A_($UHC.$Base.$fmap_27,[$__2,$x1,$x25.unR1]);
             var $__11=
              new _A_($UHC.$Base.$R1__,[$__10]);
             $__swJSW218__0=
              $__11;
             break;}
          return $__swJSW218__0;});
$UHC.$Base.$Functor_27__NEW1439UNQ10382EVLDCT74__401__0RDC=
 new _F_(function($__,$Functor_27__,$__3)
         {var $Functor_27__4=
           _e_(new _A_($UHC.$Base.$Functor_27__CLS74__395__0,[$Functor_27__]));
          var $__6=
           new _A_($UHC.$Base.$Functor_27__DCT74__401__0DFLUHC_2eBase_2efmap_27,[$__,$__3]);
          var $__7=
           {_tag_:0,_1:$__6};
          return $__7;});
$UHC.$Base.$Functor_27__NEW1435UNQ10379DCT74__401__0RDC=
 new _F_(function($__,$Functor_27__,$__3)
         {var $Functor_27__4=
           new _A_($UHC.$Base.$Functor_27__NEW1439UNQ10382EVLDCT74__401__0RDC,[$__,$Functor_27__,$__3]);
          return $Functor_27__4;});
$UHC.$Base.$Functor_27__DCT74__401__0=
 new _F_(function($__,$__2)
         {var $Functor_27__=
           _i_();
          _i_set_($Functor_27__,new _A_($UHC.$Base.$Functor_27__NEW1435UNQ10379DCT74__401__0RDC,[$__,$Functor_27__,$__2]));
          return $Functor_27__;});
$UHC.$Base.$__76__44143__2__2UNQ10310=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Functor_27__DCT74__401__0,[$UHC.$Base.$__76__44143__2__3UNQ10311,$UHC.$Base.$__76__44143__2__5UNQ10306]);}),[]);
$UHC.$Base.$fmap_27=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._1;});
$UHC.$Base.$Functor_27__DCT74__400__0DFLUHC_2eBase_2efmap_27=
 new _F_(function($__,$f,$__3)
         {return new _A_($UHC.$Base.$fmap_27,[$__,$f,$__3]);});
$UHC.$Base.$Functor_27__CLS74__395__0=
 new _F_(function($Functor_27__)
         {var $Functor_27__2=
           {_tag_:0,_1:$UHC.$Base.$undefined};
          return $Functor_27__2;});
$UHC.$Base.$Functor_27__NEW1423UNQ10369EVLDCT74__400__0RDC=
 new _F_(function($Functor_27__,$__)
         {var $Functor_27__3=
           _e_(new _A_($UHC.$Base.$Functor_27__CLS74__395__0,[$Functor_27__]));
          var $__5=
           new _A_($UHC.$Base.$Functor_27__DCT74__400__0DFLUHC_2eBase_2efmap_27,[$__]);
          var $__6=
           {_tag_:0,_1:$__5};
          return $__6;});
$UHC.$Base.$Functor_27__NEW1420UNQ10367DCT74__400__0RDC=
 new _F_(function($Functor_27__,$__)
         {var $Functor_27__3=
           new _A_($UHC.$Base.$Functor_27__NEW1423UNQ10369EVLDCT74__400__0RDC,[$Functor_27__,$__]);
          return $Functor_27__3;});
$UHC.$Base.$Functor_27__DCT74__400__0=
 new _F_(function($__)
         {var $Functor_27__=
           _i_();
          _i_set_($Functor_27__,new _A_($UHC.$Base.$Functor_27__NEW1420UNQ10367DCT74__400__0RDC,[$Functor_27__,$__]));
          return $Functor_27__;});
$UHC.$Base.$__76__44151__0__4__0UNQ10308=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Functor_27__DCT74__400__0,[$UHC.$Base.$__76__44143__2__2UNQ10310]);}),[]);
$UHC.$Base.$Functor__DCT74__404__0DFLUHC_2eBase_2efmap=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$fmapDefault,[$UHC.$Base.$__Rep1MaybeGENRepresentable1,$UHC.$Base.$__76__44151__0__4__0UNQ10308,$UHC.$Base.$undefined]);}),[]);
$UHC.$Base.$Functor__UNQ10305DCT74__404__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Functor__NEW3730UNQ10305DCT74__404__0RDC,[$UHC.$Base.$Functor__DCT74__404__0DFLUHC_2eBase_2efmap,$UHC.$Base.$Functor__UNQ10305DCT74__404__0RDC]);}),[]);
$UHC.$Base.$Functor__DCT74__404__0=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$Functor__UNQ10305DCT74__404__0RDC;}),[]);
$ParseLib.$Abstract.$Core.$parse=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$id;}),[]);
$ParseLib.$Abstract.$Core.$failp=
 new _A_(new _F_(function()
                 {return new _A_($Control.$Applicative.$empty,[$ParseLib.$Abstract.$Core.$Alternative__DCT142__2__0]);}),[]);
$ParseLib.$Abstract.$Derived.$__152__53__0=
 new _F_(function($xs)
         {var $__=
           new _A_($UHC.$Base.$null,[$xs]);
          var $__3=
           _e_($__);
          var $__swJSW222__0;
          switch($__3._tag_)
           {case 0:
             $__swJSW222__0=
              $ParseLib.$Abstract.$Core.$failp;
             break;
            case 1:
             var $__4=
              new _A_($ParseLib.$Abstract.$Core.$succeed,[[]]);
             $__swJSW222__0=
              $__4;
             break;}
          return $__swJSW222__0;});
$ParseLib.$Abstract.$Core.$look=
 new _F_(function($xs)
         {var $__=
           [$xs,$xs];
          return new _A_($UHC.$Base.$_3a,[$__,$UHC.$Base.$_5b_5d]);});
$ParseLib.$Abstract.$Core.$Monad__DCT142__4__0DFLUHC_2eBase_2ereturn=
 new _A_(new _F_(function()
                 {return new _A_($Control.$Applicative.$pure,[$ParseLib.$Abstract.$Core.$Applicative__DCT142__1__0]);}),[]);
$ParseLib.$Simple.$Core.$_24okUNQ54=
 new _F_(function($_24x)
         {var $__=
           _e_($_24x);
          var $__5=
           [$__[0],$__[1]];
          var $__6=
           new _A_($UHC.$Base.$_3a,[$__5,$UHC.$Base.$_5b_5d]);
          return $__6;});
$ParseLib.$Simple.$Core.$_24okUNQ43=
 new _F_(function($f,$_24x)
         {var $__=
           _e_($_24x);
          var $__6=
           new _A_($f,[$__[0],$__[1]]);
          return new _A_($UHC.$Base.$concatMap,[$ParseLib.$Simple.$Core.$_24okUNQ54,$__6]);});
$ParseLib.$Simple.$Core.$_3e_3e_3d=
 new _F_(function($p,$f,$xs)
         {var $__=
           new _A_($p,[$xs]);
          var $__5=
           new _A_($ParseLib.$Simple.$Core.$_24okUNQ43,[$f]);
          return new _A_($UHC.$Base.$concatMap,[$__5,$__]);});
$ParseLib.$Abstract.$Core.$Monad__DCT142__4__0DFLUHC_2eBase_2e_3e_3e_3d=
 new _F_(function($p,$f)
         {var $__=
           new _A_($UHC.$Base.$_2e,[$UHC.$Base.$id,$f]);
          return new _A_($ParseLib.$Simple.$Core.$_3e_3e_3d,[$p,$__]);});
$ParseLib.$Abstract.$Core.$Monad__NEW65UNQ85EVLDCT142__4__0RDC=
 new _F_(function($Monad__,$Monad__2)
         {var $Monad__3=
           _e_(new _A_($UHC.$Base.$Monad__CLS74__45__0,[$Monad__]));
          var $__8=
           {_tag_:0,_1:$Monad__3._1,_2:$ParseLib.$Abstract.$Core.$Monad__DCT142__4__0DFLUHC_2eBase_2e_3e_3e_3d,_3:$Monad__3._3,_4:$Monad__2};
          return $__8;});
$ParseLib.$Abstract.$Core.$Monad__NEW62UNQ83DCT142__4__0RDC=
 new _F_(function($Monad__,$Monad__2)
         {var $Monad__3=
           new _A_($ParseLib.$Abstract.$Core.$Monad__NEW65UNQ85EVLDCT142__4__0RDC,[$Monad__,$Monad__2]);
          return $Monad__3;});
$ParseLib.$Abstract.$Core.$Monad__UNQ83DCT142__4__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($ParseLib.$Abstract.$Core.$Monad__NEW62UNQ83DCT142__4__0RDC,[$ParseLib.$Abstract.$Core.$Monad__UNQ83DCT142__4__0RDC,$ParseLib.$Abstract.$Core.$Monad__DCT142__4__0DFLUHC_2eBase_2ereturn]);}),[]);
$ParseLib.$Abstract.$Core.$Monad__DCT142__4__0=
 new _A_(new _F_(function()
                 {return $ParseLib.$Abstract.$Core.$Monad__UNQ83DCT142__4__0RDC;}),[]);
$ParseLib.$Abstract.$Derived.$eof=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3e_3e_3d,[$ParseLib.$Abstract.$Core.$Monad__DCT142__4__0,$ParseLib.$Abstract.$Core.$look,$ParseLib.$Abstract.$Derived.$__152__53__0]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$startParse=
 new _F_(function($p)
         {var $__=
           new _A_($ParseLib.$Abstract.$Derived.$_3c_2a,[$p,$ParseLib.$Abstract.$Derived.$eof]);
          return new _A_($ParseLib.$Abstract.$Core.$parse,[$__]);});
$UHC.$Base.$snd=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return $__2[1];});
$UHC.$Base.$_24okUNQ3578=
 new _F_(function($p,$_24x)
         {var $__=
           new _A_($p,[$_24x]);
          var $__4=
           _e_($__);
          var $__swJSW227__0;
          switch($__4._tag_)
           {case 0:
             $__swJSW227__0=
              $UHC.$Base.$_5b_5d;
             break;
            case 1:
             var $__5=
              new _A_($UHC.$Base.$_3a,[$_24x,$UHC.$Base.$_5b_5d]);
             $__swJSW227__0=
              $__5;
             break;}
          return $__swJSW227__0;});
$UHC.$Base.$filter=
 new _F_(function($p,$xs)
         {var $__=
           new _A_($UHC.$Base.$_24okUNQ3578,[$p]);
          return new _A_($UHC.$Base.$concatMap,[$__,$xs]);});
$Data.$Maybe.$listToMaybe=
 new _F_(function($x1)
         {var $__=
           _e_($x1);
          var $__swJSW228__0;
          switch($__._tag_)
           {case 0:
             var $__5=
              new _A_($UHC.$Base.$Just__,[$__._1]);
             $__swJSW228__0=
              $__5;
             break;
            case 1:
             $__swJSW228__0=
              $UHC.$Base.$Nothing__;
             break;}
          return $__swJSW228__0;});
$Data.$List.$find=
 new _F_(function($p)
         {var $__=
           new _A_($UHC.$Base.$filter,[$p]);
          return new _A_($UHC.$Base.$_2e,[$Data.$Maybe.$listToMaybe,$__]);});
$UHC.$Base.$fst=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return $__2[0];});
$Models.$run=
 new _F_(function($p,$as)
         {var $__=
           new _A_($Language.$Prolog.$NanoProlog.$ParserUUTC.$startParse,[$p,$as]);
          var $__4=
           new _A_($UHC.$Base.$_2e,[$UHC.$Base.$null,$UHC.$Base.$snd]);
          var $__5=
           new _A_($Data.$List.$find,[$__4]);
          var $__6=
           new _A_($UHC.$Base.$fmap,[$UHC.$Base.$Functor__DCT74__404__0,$UHC.$Base.$fst]);
          var $__7=
           new _A_($UHC.$Base.$_2e,[$__6,$__5]);
          return new _A_($UHC.$Base.$_24,[$__7,$__]);});
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__253=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,[":-"]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__252=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$ParserUUTC.$token,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__253]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__250=
 new _A_(new _F_(function()
                 {return new _A_($ParseLib.$Abstract.$Derived.$_2a_3e,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__252,$Language.$Prolog.$NanoProlog.$ParserUUTC.$pTerms]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__248=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$ParserUUTC.$opt,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__250,$UHC.$Base.$_5b_5d]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$_3a_3c_2d_3a=
 new _F_(function($x1,$x2)
         {return {_tag_:0,_1:$x1,_2:$x2};});
$ParseLib.$Abstract.$Applications.$bracketed=
 new _F_(function($p)
         {var $__=
           new _A_($ParseLib.$Abstract.$Derived.$symbol,[$UHC.$Base.$Eq__DCT74__56__0,93]);
          var $__3=
           new _A_($ParseLib.$Abstract.$Derived.$symbol,[$UHC.$Base.$Eq__DCT74__56__0,91]);
          return new _A_($ParseLib.$Abstract.$Derived.$pack,[$__3,$p,$__]);});
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__232__0=
 new _F_(function($_24x__65__13__0)
         {return new _A_($UHC.$Base.$_3a,[$_24x__65__13__0,$UHC.$Base.$_5b_5d]);});
$Control.$Applicative.$__185__37__0=
 new _F_(function($__,$__2,$f,$a)
         {var $__5=
           new _A_($Control.$Applicative.$_3c_24_3e,[$__,$f,$a]);
          return new _A_($Control.$Applicative.$_3c_2a_3e,[$__2,$__5]);});
$Control.$Applicative.$__183__1001__2__0NEW16UNQ325=
 new _F_(function($__)
         {var $Functor__=
           _e_($__);
          return $Functor__._3;});
$Control.$Applicative.$liftA2=
 new _F_(function($__)
         {var $__2=
           new _A_($Control.$Applicative.$__183__1001__2__0NEW16UNQ325,[$__]);
          return new _A_($Control.$Applicative.$__185__37__0,[$__2,$__]);});
$UHC.$Base.$_24=
 new _F_(function($f)
         {return $f;});
$Control.$Applicative.$_3c_2a_2a_3e=
 new _F_(function($__)
         {var $__2=
           new _A_($UHC.$Base.$flip,[$UHC.$Base.$_24]);
          return new _A_($Control.$Applicative.$liftA2,[$__,$__2]);});
$Language.$Prolog.$NanoProlog.$ParserUUTC.$_3c_3f_3f_3e=
 new _F_(function($p,$q)
         {var $__=
           new _A_($Language.$Prolog.$NanoProlog.$ParserUUTC.$opt,[$q,$UHC.$Base.$id]);
          return new _A_($Control.$Applicative.$_3c_2a_2a_3e,[$ParseLib.$Abstract.$Core.$Applicative__DCT142__1__0,$p,$__]);});
$Language.$Prolog.$NanoProlog.$ParserUUTC.$pChainr=
 new _F_(function($op,$x)
         {var $__=
           new _A_($Control.$Applicative.$_3c_24_3e,[$ParseLib.$Abstract.$Core.$Functor__DCT142__0__0,$UHC.$Base.$flip,$op]);
          var $__4=
           _i_();
          var $r=
           _i_();
          _i_set_($__4,new _A_($Control.$Applicative.$_3c_2a_3e,[$ParseLib.$Abstract.$Core.$Applicative__DCT142__1__0,$__,$r]));
          _i_set_($r,new _A_($Language.$Prolog.$NanoProlog.$ParserUUTC.$_3c_3f_3f_3e,[$x,$__4]));
          return $r;});
$UHC.$Base.$concat=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$foldr,[$UHC.$Base.$_2b_2b,$UHC.$Base.$_5b_5d]);}),[]);
$UHC.$Base.$null=
 new _F_(function($x1)
         {var $__=
           _e_($x1);
          var $__swJSW231__0;
          switch($__._tag_)
           {case 0:
             $__swJSW231__0=
              $UHC.$Base.$False__;
             break;
            case 1:
             $__swJSW231__0=
              $UHC.$Base.$True__;
             break;}
          return $__swJSW231__0;});
$ParseLib.$Simple.$Core.$_3c_3c_7c_3e=
 new _F_(function($p,$q,$xs)
         {var $r=
           new _A_($p,[$xs]);
          var $__=
           new _A_($UHC.$Base.$null,[$r]);
          var $__6=
           _e_($__);
          var $__swJSW232__0;
          switch($__6._tag_)
           {case 0:
             $__swJSW232__0=
              $r;
             break;
            case 1:
             var $__7=
              new _A_($q,[$xs]);
             $__swJSW232__0=
              $__7;
             break;}
          return $__swJSW232__0;});
$ParseLib.$Abstract.$Core.$_3c_3c_7c_3e=
 new _F_(function($p,$q)
         {return new _A_($ParseLib.$Simple.$Core.$_3c_3c_7c_3e,[$p,$q]);});
$Language.$Prolog.$NanoProlog.$ParserUUTC.$opt=
 new _F_(function($p,$v)
         {var $__=
           new _A_($Control.$Applicative.$pure,[$ParseLib.$Abstract.$Core.$Applicative__DCT142__1__0,$v]);
          return new _A_($ParseLib.$Abstract.$Core.$_3c_3c_7c_3e,[$p,$__]);});
$Language.$Prolog.$NanoProlog.$ParserUUTC.$pDot=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$ParserUUTC.$symbol,[46]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$pSepDot=
 new _F_(function($p)
         {var $__=
           new _A_($Control.$Applicative.$_3c_24_3e,[$ParseLib.$Abstract.$Core.$Functor__DCT142__0__0,$UHC.$Base.$_3a,$Language.$Prolog.$NanoProlog.$ParserUUTC.$pDot]);
          var $__3=
           new _A_($Control.$Applicative.$_3c_2a_3e,[$ParseLib.$Abstract.$Core.$Applicative__DCT142__1__0,$__,$p]);
          var $__4=
           new _A_($ParseLib.$Abstract.$Derived.$many,[$__3]);
          var $__5=
           new _A_($Control.$Applicative.$_3c_24_3e,[$ParseLib.$Abstract.$Core.$Functor__DCT142__0__0,$UHC.$Base.$_3a,$p]);
          return new _A_($Control.$Applicative.$_3c_2a_3e,[$ParseLib.$Abstract.$Core.$Applicative__DCT142__1__0,$__5,$__4]);});
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__138=
 new _A_(new _F_(function()
                 {return new _A_($ParseLib.$Abstract.$Derived.$many1,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$pDigit]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__137=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$ParserUUTC.$pSepDot,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__138]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__135=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$ParserUUTC.$opt,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__137,$UHC.$Base.$_5b_5d]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__132=
 new _A_(new _F_(function()
                 {return new _A_($Control.$Applicative.$_3c_24_3e,[$ParseLib.$Abstract.$Core.$Functor__DCT142__0__0,$UHC.$Base.$concat,$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__135]);}),[]);
$ParseLib.$Abstract.$Derived.$some=
 new _F_(function($p)
         {var $__=
           new _A_($ParseLib.$Abstract.$Derived.$many,[$p]);
          var $__3=
           new _A_($Control.$Applicative.$_3c_24_3e,[$ParseLib.$Abstract.$Core.$Functor__DCT142__0__0,$UHC.$Base.$_3a,$p]);
          return new _A_($Control.$Applicative.$_3c_2a_3e,[$ParseLib.$Abstract.$Core.$Applicative__DCT142__1__0,$__3,$__]);});
$ParseLib.$Abstract.$Derived.$many1=
 new _A_(new _F_(function()
                 {return $ParseLib.$Abstract.$Derived.$some;}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__131=
 new _A_(new _F_(function()
                 {return new _A_($ParseLib.$Abstract.$Derived.$many1,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$pUpper]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__128=
 new _A_(new _F_(function()
                 {return new _A_($Control.$Applicative.$_3c_24_3e,[$ParseLib.$Abstract.$Core.$Functor__DCT142__0__0,$UHC.$Base.$_2b_2b,$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__131]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__125=
 new _A_(new _F_(function()
                 {return new _A_($Control.$Applicative.$_3c_2a_3e,[$ParseLib.$Abstract.$Core.$Applicative__DCT142__1__0,$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__128,$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__132]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__124=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$ParserUUTC.$lexeme,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__125]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$pVar=
 new _A_(new _F_(function()
                 {return new _A_($Control.$Applicative.$_3c_24_3e,[$ParseLib.$Abstract.$Core.$Functor__DCT142__0__0,$Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__124]);}),[]);
$ParseLib.$Abstract.$Derived.$listOf=
 new _F_(function($p,$s)
         {var $__=
           new _A_($ParseLib.$Abstract.$Derived.$_2a_3e,[$s,$p]);
          var $__4=
           new _A_($ParseLib.$Abstract.$Derived.$many,[$__]);
          var $__5=
           new _A_($Control.$Applicative.$_3c_24_3e,[$ParseLib.$Abstract.$Core.$Functor__DCT142__0__0,$UHC.$Base.$_3a,$p]);
          return new _A_($Control.$Applicative.$_3c_2a_3e,[$ParseLib.$Abstract.$Core.$Applicative__DCT142__1__0,$__5,$__4]);});
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__192__0=
 new _F_(function($h,$t)
         {var $__=
           new _A_($UHC.$Base.$_3a,[$t,$UHC.$Base.$_5b_5d]);
          var $__4=
           new _A_($UHC.$Base.$_3a,[$h,$__]);
          var $__5=
           new _A_($UHC.$Base.$packedStringToString,["cons"]);
          return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$__5,$__4]);});
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__203=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$ParserUUTC.$symbol,[58]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__190=
 new _A_(new _F_(function()
                 {return new _A_($ParseLib.$Abstract.$Derived.$_3c_24,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__192__0,$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__203]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__175__0=
 new _F_(function($f,$a)
         {var $__=
           new _A_($UHC.$Base.$_3a,[$a,$UHC.$Base.$_5b_5d]);
          var $__4=
           new _A_($UHC.$Base.$_3a,[$f,$__]);
          var $__5=
           new _A_($UHC.$Base.$packedStringToString,["->"]);
          return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$__5,$__4]);});
$ParseLib.$Abstract.$Derived.$token=
 new _F_(function($__,$x1)
         {var $__3=
           _e_($x1);
          var $__swJSW233__0;
          switch($__3._tag_)
           {case 0:
             var $__6=
              new _A_($ParseLib.$Abstract.$Derived.$token,[$__,$__3._2]);
             var $__7=
              new _A_($ParseLib.$Abstract.$Derived.$symbol,[$__,$__3._1]);
             var $__8=
              new _A_($Control.$Applicative.$_3c_24_3e,[$ParseLib.$Abstract.$Core.$Functor__DCT142__0__0,$UHC.$Base.$_3a,$__7]);
             var $__9=
              new _A_($Control.$Applicative.$_3c_2a_3e,[$ParseLib.$Abstract.$Core.$Applicative__DCT142__1__0,$__8,$__6]);
             $__swJSW233__0=
              $__9;
             break;
            case 1:
             var $__10=
              new _A_($ParseLib.$Abstract.$Core.$succeed,[$UHC.$Base.$_5b_5d]);
             $__swJSW233__0=
              $__10;
             break;}
          return $__swJSW233__0;});
$Language.$Prolog.$NanoProlog.$ParserUUTC.$token=
 new _F_(function($t)
         {var $__=
           new _A_($ParseLib.$Abstract.$Derived.$token,[$UHC.$Base.$Eq__DCT74__56__0,$t]);
          return new _A_($ParseLib.$Abstract.$Derived.$_3c_2a,[$__,$Language.$Prolog.$NanoProlog.$ParserUUTC.$spaces]);});
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__187=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["->"]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__186=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$ParserUUTC.$token,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__187]);}),[]);
$ParseLib.$Abstract.$Derived.$_3c_24=
 new _F_(function($f)
         {var $__=
           new _A_($UHC.$Base.$const,[$f]);
          return new _A_($Control.$Applicative.$_3c_24_3e,[$ParseLib.$Abstract.$Core.$Functor__DCT142__0__0,$__]);});
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__173=
 new _A_(new _F_(function()
                 {return new _A_($ParseLib.$Abstract.$Derived.$_3c_24,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__175__0,$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__186]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__66__1500__2__1=
 new _A_(new _F_(function()
                 {var $Applicative__=
                   _e_($ParseLib.$Abstract.$Core.$Alternative__DCT142__2__0);
                  return $Applicative__._2;}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__66__1609__2__0=
 new _A_(new _F_(function()
                 {var $Functor__=
                   _e_($Language.$Prolog.$NanoProlog.$ParserUUTC.$__66__1500__2__1);
                  return $Functor__._3;}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$lexeme=
 new _F_(function($p)
         {return new _A_($ParseLib.$Abstract.$Derived.$_3c_2a,[$p,$Language.$Prolog.$NanoProlog.$ParserUUTC.$spaces]);});
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__113=
 new _A_(new _F_(function()
                 {return new _A_($Control.$Applicative.$_3c_24_3e,[$ParseLib.$Abstract.$Core.$Functor__DCT142__0__0,$UHC.$Base.$_3a,$Language.$Prolog.$NanoProlog.$ParserUUTC.$pLower]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__41=
 new _A_(new _F_(function()
                 {return [65,90];}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$pUpper=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$ParserUUTC.$pRange,[$UHC.$Base.$Enum__DCT74__60__0,$UHC.$Base.$Eq__DCT74__56__0,$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__41]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__96=
 new _A_(new _F_(function()
                 {return [97,122];}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$pLower=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$ParserUUTC.$pRange,[$UHC.$Base.$Enum__DCT74__60__0,$UHC.$Base.$Eq__DCT74__56__0,$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__96]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$pLetter=
 new _A_(new _F_(function()
                 {return new _A_($Control.$Applicative.$_3c_7c_3e,[$ParseLib.$Abstract.$Core.$Alternative__DCT142__2__0,$Language.$Prolog.$NanoProlog.$ParserUUTC.$pUpper,$Language.$Prolog.$NanoProlog.$ParserUUTC.$pLower]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$pRange=
 new _F_(function($__,$__2,$__3)
         {var $__4=
           _e_($__3);
          var $__7=
           new _A_($UHC.$Base.$enumFromTo,[$__,$__4[0],$__4[1]]);
          var $__8=
           new _A_($ParseLib.$Abstract.$Derived.$symbol,[$__2]);
          var $__9=
           new _A_($UHC.$Base.$map,[$__8,$__7]);
          var $__10=
           new _A_($ParseLib.$Abstract.$Derived.$choice,[$__9]);
          return $__10;});
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__106=
 new _A_(new _F_(function()
                 {return [48,57];}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$pDigit=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$ParserUUTC.$pRange,[$UHC.$Base.$Enum__DCT74__60__0,$UHC.$Base.$Eq__DCT74__56__0,$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__106]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__117=
 new _A_(new _F_(function()
                 {return new _A_($Control.$Applicative.$_3c_7c_3e,[$ParseLib.$Abstract.$Core.$Alternative__DCT142__2__0,$Language.$Prolog.$NanoProlog.$ParserUUTC.$pLetter,$Language.$Prolog.$NanoProlog.$ParserUUTC.$pDigit]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__116=
 new _A_(new _F_(function()
                 {return new _A_($ParseLib.$Abstract.$Derived.$many,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__117]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__110=
 new _A_(new _F_(function()
                 {return new _A_($Control.$Applicative.$_3c_2a_3e,[$ParseLib.$Abstract.$Core.$Applicative__DCT142__1__0,$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__113,$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__116]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$pLowerCase=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$ParserUUTC.$lexeme,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__110]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__217=
 new _A_(new _F_(function()
                 {return new _A_($Control.$Applicative.$_3c_24_3e,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$__66__1609__2__0,$Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,$Language.$Prolog.$NanoProlog.$ParserUUTC.$pLowerCase]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__227=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["[]"]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__226=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__227]);}),[]);
$Control.$Applicative.$pure=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._2;});
$ParseLib.$Abstract.$Core.$succeed=
 new _A_(new _F_(function()
                 {return new _A_($Control.$Applicative.$pure,[$ParseLib.$Abstract.$Core.$Applicative__DCT142__1__0]);}),[]);
$ParseLib.$Abstract.$Derived.$many=
 new _F_(function($p)
         {var $__=
           new _A_($ParseLib.$Abstract.$Core.$succeed,[$UHC.$Base.$_5b_5d]);
          var $__3=
           new _A_($ParseLib.$Abstract.$Derived.$many,[$p]);
          var $__4=
           new _A_($Control.$Applicative.$_3c_24_3e,[$ParseLib.$Abstract.$Core.$Functor__DCT142__0__0,$UHC.$Base.$_3a,$p]);
          var $__5=
           new _A_($Control.$Applicative.$_3c_2a_3e,[$ParseLib.$Abstract.$Core.$Applicative__DCT142__1__0,$__4,$__3]);
          return new _A_($Control.$Applicative.$_3c_7c_3e,[$ParseLib.$Abstract.$Core.$Alternative__DCT142__2__0,$__5,$__]);});
$Control.$Applicative.$_3c_7c_3e=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._1;});
$ParseLib.$Abstract.$Derived.$__152__80=
 new _A_(new _F_(function()
                 {return new _A_($Control.$Applicative.$_3c_7c_3e,[$ParseLib.$Abstract.$Core.$Alternative__DCT142__2__0]);}),[]);
$Control.$Applicative.$Alternative__CLS181__1__0=
 new _F_(function($Alternative__)
         {var $Alternative__2=
           {_tag_:0,_1:$UHC.$Base.$undefined,_2:$UHC.$Base.$undefined,_3:$UHC.$Base.$undefined};
          return $Alternative__2;});
$ParseLib.$Simple.$Core.$empty=
 new _F_(function($xs)
         {return $UHC.$Base.$_5b_5d;});
$ParseLib.$Simple.$Core.$_3c_7c_3e=
 new _F_(function($p,$q,$xs)
         {var $__=
           new _A_($q,[$xs]);
          var $__5=
           new _A_($p,[$xs]);
          return new _A_($UHC.$Base.$_2b_2b,[$__5,$__]);});
$ParseLib.$Abstract.$Core.$Alternative__DCT142__2__0DFLControl_2eApplicative_2e_3c_7c_3e=
 new _F_(function($p,$q)
         {return new _A_($ParseLib.$Simple.$Core.$_3c_7c_3e,[$p,$q]);});
$ParseLib.$Abstract.$Core.$Alternative__NEW41UNQ94EVLDCT142__2__0RDC=
 new _F_(function($Alternative__)
         {var $Alternative__2=
           _e_(new _A_($Control.$Applicative.$Alternative__CLS181__1__0,[$Alternative__]));
          var $__6=
           {_tag_:0,_1:$ParseLib.$Abstract.$Core.$Alternative__DCT142__2__0DFLControl_2eApplicative_2e_3c_7c_3e,_2:$ParseLib.$Abstract.$Core.$Applicative__DCT142__1__0,_3:$ParseLib.$Simple.$Core.$empty};
          return $__6;});
$ParseLib.$Abstract.$Core.$Alternative__NEW39UNQ93DCT142__2__0RDC=
 new _F_(function($Alternative__)
         {var $Alternative__2=
           new _A_($ParseLib.$Abstract.$Core.$Alternative__NEW41UNQ94EVLDCT142__2__0RDC,[$Alternative__]);
          return $Alternative__2;});
$ParseLib.$Abstract.$Core.$Alternative__UNQ93DCT142__2__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($ParseLib.$Abstract.$Core.$Alternative__NEW39UNQ93DCT142__2__0RDC,[$ParseLib.$Abstract.$Core.$Alternative__UNQ93DCT142__2__0RDC]);}),[]);
$ParseLib.$Abstract.$Core.$Alternative__DCT142__2__0=
 new _A_(new _F_(function()
                 {return $ParseLib.$Abstract.$Core.$Alternative__UNQ93DCT142__2__0RDC;}),[]);
$Control.$Applicative.$empty=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._3;});
$ParseLib.$Abstract.$Derived.$__152__81=
 new _A_(new _F_(function()
                 {return new _A_($Control.$Applicative.$empty,[$ParseLib.$Abstract.$Core.$Alternative__DCT142__2__0]);}),[]);
$ParseLib.$Abstract.$Derived.$choice=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$foldr,[$ParseLib.$Abstract.$Derived.$__152__80,$ParseLib.$Abstract.$Derived.$__152__81]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__48=
 new _A_(new _F_(function()
                 {return new _A_($ParseLib.$Abstract.$Derived.$symbol,[$UHC.$Base.$Eq__DCT74__56__0,32]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__60=
 new _A_(new _F_(function()
                 {return new _A_($ParseLib.$Abstract.$Derived.$symbol,[$UHC.$Base.$Eq__DCT74__56__0,9]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__58=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__60,$UHC.$Base.$_5b_5d]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__56=
 new _A_(new _F_(function()
                 {return new _A_($ParseLib.$Abstract.$Derived.$symbol,[$UHC.$Base.$Eq__DCT74__56__0,10]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__54=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__56,$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__58]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__52=
 new _A_(new _F_(function()
                 {return new _A_($ParseLib.$Abstract.$Derived.$symbol,[$UHC.$Base.$Eq__DCT74__56__0,13]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__50=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__52,$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__54]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__46=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__48,$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__50]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__45=
 new _A_(new _F_(function()
                 {return new _A_($ParseLib.$Abstract.$Derived.$choice,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__46]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$spaces=
 new _A_(new _F_(function()
                 {return new _A_($ParseLib.$Abstract.$Derived.$many,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__45]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$symbol=
 new _F_(function($c)
         {var $__=
           new _A_($ParseLib.$Abstract.$Derived.$symbol,[$UHC.$Base.$Eq__DCT74__56__0,$c]);
          return new _A_($ParseLib.$Abstract.$Derived.$_3c_2a,[$__,$Language.$Prolog.$NanoProlog.$ParserUUTC.$spaces]);});
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__238=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$ParserUUTC.$symbol,[44]);}),[]);
$ParseLib.$Abstract.$Derived.$__152__8__0=
 new _F_(function($__,$x,$_24x__149__5__0)
         {return new _A_($UHC.$Base.$_3d_3d,[$__,$_24x__149__5__0,$x]);});
$ParseLib.$Simple.$Core.$satisfy=
 new _F_(function($x1,$x2)
         {var $x23=
           _e_($x2);
          var $__swJSW241__0;
          switch($x23._tag_)
           {case 0:
             var $__=
              new _A_($x1,[$x23._1]);
             var $__7=
              _e_($__);
             var $__swJSW242__0;
             switch($__7._tag_)
              {case 0:
                $__swJSW242__0=
                 $UHC.$Base.$_5b_5d;
                break;
               case 1:
                var $__8=
                 [$x23._1,$x23._2];
                var $__9=
                 new _A_($UHC.$Base.$_3a,[$__8,$UHC.$Base.$_5b_5d]);
                $__swJSW242__0=
                 $__9;
                break;}
             $__swJSW241__0=
              $__swJSW242__0;
             break;
            case 1:
             $__swJSW241__0=
              $UHC.$Base.$_5b_5d;
             break;}
          return $__swJSW241__0;});
$ParseLib.$Abstract.$Core.$satisfy=
 new _A_(new _F_(function()
                 {return $ParseLib.$Simple.$Core.$satisfy;}),[]);
$ParseLib.$Abstract.$Derived.$symbol=
 new _F_(function($__,$x)
         {var $__3=
           new _A_($ParseLib.$Abstract.$Derived.$__152__8__0,[$__,$x]);
          return new _A_($ParseLib.$Abstract.$Core.$satisfy,[$__3]);});
$ParseLib.$Abstract.$Derived.$_2a_3e=
 new _F_(function($p)
         {var $__=
           new _A_($UHC.$Base.$flip,[$UHC.$Base.$const]);
          var $__3=
           new _A_($Control.$Applicative.$_3c_24_3e,[$ParseLib.$Abstract.$Core.$Functor__DCT142__0__0,$__,$p]);
          return new _A_($Control.$Applicative.$_3c_2a_3e,[$ParseLib.$Abstract.$Core.$Applicative__DCT142__1__0,$__3]);});
$ParseLib.$Abstract.$Derived.$pack=
 new _F_(function($p,$r)
         {var $__=
           new _A_($ParseLib.$Abstract.$Derived.$_2a_3e,[$p,$r]);
          return new _A_($ParseLib.$Abstract.$Derived.$_3c_2a,[$__]);});
$ParseLib.$Abstract.$Applications.$parenthesised=
 new _F_(function($p)
         {var $__=
           new _A_($ParseLib.$Abstract.$Derived.$symbol,[$UHC.$Base.$Eq__DCT74__56__0,41]);
          var $__3=
           new _A_($ParseLib.$Abstract.$Derived.$symbol,[$UHC.$Base.$Eq__DCT74__56__0,40]);
          return new _A_($ParseLib.$Abstract.$Derived.$pack,[$__3,$p,$__]);});
$Language.$Prolog.$NanoProlog.$ParserUUTC.$pFun=
 new _A_(new _F_(function()
                 {return new _A_($Control.$Applicative.$_3c_7c_3e,[$ParseLib.$Abstract.$Core.$Alternative__DCT142__2__0,$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__214,$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__223]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__214=
 new _A_(new _F_(function()
                 {return new _A_($Control.$Applicative.$_3c_2a_3e,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$__66__1500__2__1,$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__217,$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__220]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__220=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$ParserUUTC.$opt,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__222,$UHC.$Base.$_5b_5d]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__222=
 new _A_(new _F_(function()
                 {return new _A_($ParseLib.$Abstract.$Applications.$parenthesised,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$pTerms]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$pTerms=
 new _A_(new _F_(function()
                 {return new _A_($ParseLib.$Abstract.$Derived.$listOf,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$pTerm,$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__238]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$pTerm=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$ParserUUTC.$pChainr,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__173,$Language.$Prolog.$NanoProlog.$ParserUUTC.$pCons]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$pCons=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$ParserUUTC.$pChainr,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__190,$Language.$Prolog.$NanoProlog.$ParserUUTC.$pFactor]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$pFactor=
 new _A_(new _F_(function()
                 {return new _A_($Control.$Applicative.$_3c_7c_3e,[$ParseLib.$Abstract.$Core.$Alternative__DCT142__2__0,$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__207,$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__210]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__207=
 new _A_(new _F_(function()
                 {return new _A_($Control.$Applicative.$_3c_7c_3e,[$ParseLib.$Abstract.$Core.$Alternative__DCT142__2__0,$Language.$Prolog.$NanoProlog.$ParserUUTC.$pVar,$Language.$Prolog.$NanoProlog.$ParserUUTC.$pFun]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__210=
 new _A_(new _F_(function()
                 {return new _A_($ParseLib.$Abstract.$Applications.$parenthesised,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$pTerm]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__223=
 new _A_(new _F_(function()
                 {return new _A_($Control.$Applicative.$_3c_24_3e,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$__66__1609__2__0,$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__226,$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__228]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__228=
 new _A_(new _F_(function()
                 {return new _A_($ParseLib.$Abstract.$Applications.$bracketed,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__229]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__229=
 new _A_(new _F_(function()
                 {return new _A_($Control.$Applicative.$_3c_24_3e,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$__66__1609__2__0,$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__232__0,$Language.$Prolog.$NanoProlog.$ParserUUTC.$pTerm]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__245=
 new _A_(new _F_(function()
                 {return new _A_($Control.$Applicative.$_3c_24_3e,[$ParseLib.$Abstract.$Core.$Functor__DCT142__0__0,$Language.$Prolog.$NanoProlog.$NanoProlog.$_3a_3c_2d_3a,$Language.$Prolog.$NanoProlog.$ParserUUTC.$pFun]);}),[]);
$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__242=
 new _A_(new _F_(function()
                 {return new _A_($Control.$Applicative.$_3c_2a_3e,[$ParseLib.$Abstract.$Core.$Applicative__DCT142__1__0,$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__245,$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__248]);}),[]);
$Control.$Applicative.$_3c_24_3e=
 new _F_(function($__)
         {return new _A_($UHC.$Base.$fmap,[$__]);});
$Control.$Applicative.$_3c_2a_3e=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._1;});
$UHC.$Base.$const=
 new _F_(function($k,$__)
         {return $k;});
$ParseLib.$Simple.$Core.$_24okUNQ108=
 new _F_(function($f,$_24x)
         {var $__=
           _e_($_24x);
          var $__6=
           new _A_($f,[$__[0]]);
          var $__7=
           [$__6,$__[1]];
          var $__8=
           new _A_($UHC.$Base.$_3a,[$__7,$UHC.$Base.$_5b_5d]);
          return $__8;});
$ParseLib.$Simple.$Core.$_24okUNQ97=
 new _F_(function($q,$_24x)
         {var $__=
           _e_($_24x);
          var $__6=
           new _A_($q,[$__[1]]);
          var $__7=
           new _A_($ParseLib.$Simple.$Core.$_24okUNQ108,[$__[0]]);
          return new _A_($UHC.$Base.$concatMap,[$__7,$__6]);});
$ParseLib.$Simple.$Core.$_3c_2a_3e=
 new _F_(function($p,$q,$xs)
         {var $__=
           new _A_($p,[$xs]);
          var $__5=
           new _A_($ParseLib.$Simple.$Core.$_24okUNQ97,[$q]);
          return new _A_($UHC.$Base.$concatMap,[$__5,$__]);});
$ParseLib.$Abstract.$Core.$Applicative__DCT142__1__0DFLControl_2eApplicative_2e_3c_2a_3e=
 new _F_(function($p,$q)
         {return new _A_($ParseLib.$Simple.$Core.$_3c_2a_3e,[$p,$q]);});
$Control.$Applicative.$Applicative__CLS181__0__0=
 new _F_(function($Applicative__)
         {var $Applicative__2=
           {_tag_:0,_1:$UHC.$Base.$undefined,_2:$UHC.$Base.$undefined,_3:$UHC.$Base.$undefined};
          return $Applicative__2;});
$ParseLib.$Simple.$Core.$_24okUNQ76=
 new _F_(function($f,$_24x)
         {var $__=
           _e_($_24x);
          var $__6=
           new _A_($f,[$__[0]]);
          var $__7=
           [$__6,$__[1]];
          var $__8=
           new _A_($UHC.$Base.$_3a,[$__7,$UHC.$Base.$_5b_5d]);
          return $__8;});
$ParseLib.$Simple.$Core.$_3c_24_3e=
 new _F_(function($f,$p,$xs)
         {var $__=
           new _A_($p,[$xs]);
          var $__5=
           new _A_($ParseLib.$Simple.$Core.$_24okUNQ76,[$f]);
          return new _A_($UHC.$Base.$concatMap,[$__5,$__]);});
$ParseLib.$Abstract.$Core.$Functor__DCT142__0__0DFLUHC_2eBase_2efmap=
 new _F_(function($f,$p)
         {return new _A_($ParseLib.$Simple.$Core.$_3c_24_3e,[$f,$p]);});
$ParseLib.$Abstract.$Core.$Functor__NEW15UNQ110EVLDCT142__0__0RDC=
 new _F_(function($Functor__)
         {var $Functor__2=
           _e_(new _A_($UHC.$Base.$Functor__CLS74__44__0,[$Functor__]));
          var $__4=
           {_tag_:0,_1:$ParseLib.$Abstract.$Core.$Functor__DCT142__0__0DFLUHC_2eBase_2efmap};
          return $__4;});
$ParseLib.$Abstract.$Core.$Functor__NEW13UNQ109DCT142__0__0RDC=
 new _F_(function($Functor__)
         {var $Functor__2=
           new _A_($ParseLib.$Abstract.$Core.$Functor__NEW15UNQ110EVLDCT142__0__0RDC,[$Functor__]);
          return $Functor__2;});
$ParseLib.$Abstract.$Core.$Functor__UNQ109DCT142__0__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($ParseLib.$Abstract.$Core.$Functor__NEW13UNQ109DCT142__0__0RDC,[$ParseLib.$Abstract.$Core.$Functor__UNQ109DCT142__0__0RDC]);}),[]);
$ParseLib.$Abstract.$Core.$Functor__DCT142__0__0=
 new _A_(new _F_(function()
                 {return $ParseLib.$Abstract.$Core.$Functor__UNQ109DCT142__0__0RDC;}),[]);
$ParseLib.$Simple.$Core.$succeed=
 new _F_(function($r,$xs)
         {var $__=
           [$r,$xs];
          return new _A_($UHC.$Base.$_3a,[$__,$UHC.$Base.$_5b_5d]);});
$ParseLib.$Abstract.$Core.$Applicative__NEW23UNQ102EVLDCT142__1__0RDC=
 new _F_(function($Applicative__)
         {var $Applicative__2=
           _e_(new _A_($Control.$Applicative.$Applicative__CLS181__0__0,[$Applicative__]));
          var $__6=
           {_tag_:0,_1:$ParseLib.$Abstract.$Core.$Applicative__DCT142__1__0DFLControl_2eApplicative_2e_3c_2a_3e,_2:$ParseLib.$Simple.$Core.$succeed,_3:$ParseLib.$Abstract.$Core.$Functor__DCT142__0__0};
          return $__6;});
$ParseLib.$Abstract.$Core.$Applicative__NEW21UNQ101DCT142__1__0RDC=
 new _F_(function($Applicative__)
         {var $Applicative__2=
           new _A_($ParseLib.$Abstract.$Core.$Applicative__NEW23UNQ102EVLDCT142__1__0RDC,[$Applicative__]);
          return $Applicative__2;});
$ParseLib.$Abstract.$Core.$Applicative__UNQ101DCT142__1__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($ParseLib.$Abstract.$Core.$Applicative__NEW21UNQ101DCT142__1__0RDC,[$ParseLib.$Abstract.$Core.$Applicative__UNQ101DCT142__1__0RDC]);}),[]);
$ParseLib.$Abstract.$Core.$Applicative__DCT142__1__0=
 new _A_(new _F_(function()
                 {return $ParseLib.$Abstract.$Core.$Applicative__UNQ101DCT142__1__0RDC;}),[]);
$ParseLib.$Abstract.$Derived.$_3c_2a=
 new _F_(function($p)
         {var $__=
           new _A_($Control.$Applicative.$_3c_24_3e,[$ParseLib.$Abstract.$Core.$Functor__DCT142__0__0,$UHC.$Base.$const,$p]);
          return new _A_($Control.$Applicative.$_3c_2a_3e,[$ParseLib.$Abstract.$Core.$Applicative__DCT142__1__0,$__]);});
$Language.$Prolog.$NanoProlog.$ParserUUTC.$pRule=
 new _A_(new _F_(function()
                 {return new _A_($ParseLib.$Abstract.$Derived.$_3c_2a,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$__68__242,$Language.$Prolog.$NanoProlog.$ParserUUTC.$pDot]);}),[]);
$Models.$tryParseRule=
 new _A_(new _F_(function()
                 {return new _A_($Models.$run,[$Language.$Prolog.$NanoProlog.$ParserUUTC.$pRule]);}),[]);
$Language.$UHC.$JS.$JQuery.$JQuery.$wrappedJQueryUIEvent=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_(wrappedThis($__3));
          return [$__2,$__4];});
$JCU.$checkProofStoreKey=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["checkProof"]);}),[]);
$Language.$UHC.$JS.$JQuery.$JQuery.$_24okUNQ901=
 new _F_(function($f,$jq,$ui,$_24x)
         {return new _A_($f,[$_24x,$jq,$ui]);});
$Language.$UHC.$JS.$JQuery.$JQuery.$jQueryObj=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_(jQuery($__3));
          return [$__2,$__4];});
$Language.$UHC.$JS.$JQuery.$JQuery.$gUNQ896=
 new _F_(function($f,$this,$jq,$ui)
         {var $__=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$jQueryObj,[$this]);
          var $__6=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$_24okUNQ901,[$f,$jq,$ui]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__,$__6]);});
$Language.$UHC.$JS.$JQuery.$JQuery.$__mkJUIThisEventHandler=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_(function(v1,v2,v3)
               {var res=
                 _e_(new _A_($__3,[v1,v2,v3,[]]));
                _e_(res[0]);
                return _e_(res[1]);});
          return [$__2,$__4];});
$Language.$UHC.$JS.$JQuery.$JQuery.$mkJUIThisEventHandler=
 new _F_(function($f)
         {var $__=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$gUNQ896,[$f]);
          return new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$__mkJUIThisEventHandler,[$__]);});
$UHC.$Base.$showList=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._2;});
$UHC.$Base.$Show__DCT74__87__0DFLUHC_2eBase_2eshowsPrec=
 new _F_(function($__,$p)
         {return new _A_($UHC.$Base.$showList,[$__]);});
$UHC.$Base.$Show__NEW5726UNQ11646EVLDCT74__87__0RDC=
 new _F_(function($__,$Show__)
         {var $Show__3=
           _e_(new _A_($UHC.$Base.$Show__CLS74__43__0,[$Show__]));
          var $__7=
           new _A_($UHC.$Base.$Show__DCT74__87__0DFLUHC_2eBase_2eshowsPrec,[$__]);
          var $__8=
           {_tag_:0,_1:$Show__3._1,_2:$Show__3._2,_3:$__7};
          return $__8;});
$UHC.$Base.$Show__NEW5723UNQ11644DCT74__87__0RDC=
 new _F_(function($__,$Show__)
         {var $Show__3=
           new _A_($UHC.$Base.$Show__NEW5726UNQ11646EVLDCT74__87__0RDC,[$__,$Show__]);
          return $Show__3;});
$UHC.$Base.$Show__DCT74__87__0=
 new _F_(function($__)
         {var $Show__=
           _i_();
          _i_set_($Show__,new _A_($UHC.$Base.$Show__NEW5723UNQ11644DCT74__87__0RDC,[$__,$Show__]));
          return $Show__;});
$UHC.$Base.$showParen=
 new _F_(function($b,$p)
         {var $__=
           _e_($b);
          var $__swJSW251__0;
          switch($__._tag_)
           {case 0:
             $__swJSW251__0=
              $p;
             break;
            case 1:
             var $__4=
              new _A_($UHC.$Base.$showChar,[41]);
             var $__5=
              new _A_($UHC.$Base.$_2e,[$p,$__4]);
             var $__6=
              new _A_($UHC.$Base.$showChar,[40]);
             var $__7=
              new _A_($UHC.$Base.$_2e,[$__6,$__5]);
             $__swJSW251__0=
              $__7;
             break;}
          return $__swJSW251__0;});
$Data.$Tree.$__40__0__0DFLUHC_2eBase_2eshowsPrec=
 new _F_(function($__,$__2,$d,$x__1)
         {var $x__15=
           _e_($x__1);
          var $__8=
           new _A_($UHC.$Base.$showsPrec,[$__,11,$x__15.subForest]);
          var $__9=
           new _A_($UHC.$Base.$packedStringToString,[" "]);
          var $__10=
           new _A_($UHC.$Base.$showString,[$__9]);
          var $__11=
           new _A_($UHC.$Base.$_2e,[$__10,$__8]);
          var $__12=
           new _A_($UHC.$Base.$showsPrec,[$__2,11,$x__15.rootLabel]);
          var $__13=
           new _A_($UHC.$Base.$_2e,[$__12,$__11]);
          var $__14=
           new _A_($UHC.$Base.$packedStringToString,["Node "]);
          var $__15=
           new _A_($UHC.$Base.$showString,[$__14]);
          var $__16=
           new _A_($UHC.$Base.$_2e,[$__15,$__13]);
          var $__17=
           new _A_($UHC.$Base.$primGtInt,[$d,10]);
          var $__18=
           new _A_($UHC.$Base.$showParen,[$__17,$__16]);
          return $__18;});
$Data.$Tree.$__40__0__0NEW57UNQ118EVLRDC=
 new _F_(function($__,$__2,$__3)
         {var $Show__=
           _e_(new _A_($UHC.$Base.$Show__CLS74__43__0,[$__2]));
          var $__8=
           new _A_($Data.$Tree.$__40__0__0DFLUHC_2eBase_2eshowsPrec,[$__,$__3]);
          var $__9=
           {_tag_:0,_1:$Show__._1,_2:$Show__._2,_3:$__8};
          return $__9;});
$Data.$Tree.$__40__0__0NEW53UNQ115RDC=
 new _F_(function($__,$__2,$__3)
         {var $__4=
           new _A_($Data.$Tree.$__40__0__0NEW57UNQ118EVLRDC,[$__,$__2,$__3]);
          return $__4;});
$Data.$Tree.$__40__0__0=
 new _F_(function($__)
         {var $__2=
           _i_();
          var $__3=
           _i_();
          _i_set_($__2,new _A_($UHC.$Base.$Show__DCT74__87__0,[$__3]));
          _i_set_($__3,new _A_($Data.$Tree.$__40__0__0NEW53UNQ115RDC,[$__2,$__3,$__]));
          return $__3;});
$Prolog.$__28__0__0DFLUHC_2eBase_2eshowsPrec=
 new _F_(function($d,$x__1)
         {var $x__13=
           _e_($x__1);
          var $__swJSW254__0;
          switch($x__13._tag_)
           {case 0:
             var $__=
              new _A_($UHC.$Base.$packedStringToString,["Correct"]);
             var $__5=
              new _A_($UHC.$Base.$showString,[$__]);
             $__swJSW254__0=
              $__5;
             break;
            case 1:
             var $__=
              new _A_($UHC.$Base.$packedStringToString,["Incomplete"]);
             var $__7=
              new _A_($UHC.$Base.$showString,[$__]);
             $__swJSW254__0=
              $__7;
             break;
            case 2:
             var $__=
              new _A_($UHC.$Base.$packedStringToString,["Invalid"]);
             var $__9=
              new _A_($UHC.$Base.$showString,[$__]);
             $__swJSW254__0=
              $__9;
             break;}
          return $__swJSW254__0;});
$UHC.$Base.$showString=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$_2b_2b;}),[]);
$UHC.$Base.$showChar=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$_3a;}),[]);
$UHC.$Base.$shows=
 new _F_(function($__)
         {return new _A_($UHC.$Base.$showsPrec,[$__,0]);});
$UHC.$Base.$showlUNQ8909=
 new _F_(function($__,$x1)
         {var $__3=
           _e_($x1);
          var $__swJSW255__0;
          switch($__3._tag_)
           {case 0:
             var $__6=
              new _A_($UHC.$Base.$showlUNQ8909,[$__,$__3._2]);
             var $__7=
              new _A_($UHC.$Base.$shows,[$__,$__3._1]);
             var $__8=
              new _A_($UHC.$Base.$_2e,[$__7,$__6]);
             var $__9=
              new _A_($UHC.$Base.$showChar,[44]);
             var $__10=
              new _A_($UHC.$Base.$_2e,[$__9,$__8]);
             $__swJSW255__0=
              $__10;
             break;
            case 1:
             var $__11=
              new _A_($UHC.$Base.$showChar,[93]);
             $__swJSW255__0=
              $__11;
             break;}
          return $__swJSW255__0;});
$UHC.$Base.$Show__CLS74__43__0DFLUHC_2eBase_2eshowList=
 new _F_(function($Show__,$x1)
         {var $__=
           _e_($x1);
          var $__swJSW256__0;
          switch($__._tag_)
           {case 0:
             var $__6=
              new _A_($UHC.$Base.$showlUNQ8909,[$Show__,$__._2]);
             var $__7=
              new _A_($UHC.$Base.$shows,[$Show__,$__._1]);
             var $__8=
              new _A_($UHC.$Base.$_2e,[$__7,$__6]);
             var $__9=
              new _A_($UHC.$Base.$showChar,[91]);
             $__swJSW256__0=
              new _A_($UHC.$Base.$_2e,[$__9,$__8]);
             break;
            case 1:
             var $__10=
              new _A_($UHC.$Base.$packedStringToString,["[]"]);
             var $__11=
              new _A_($UHC.$Base.$showString,[$__10]);
             $__swJSW256__0=
              $__11;
             break;}
          return $__swJSW256__0;});
$UHC.$Base.$showsPrec=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._3;});
$UHC.$Base.$Show__CLS74__43__0DFLUHC_2eBase_2eshow=
 new _F_(function($Show__,$x)
         {var $__=
           new _A_($UHC.$Base.$packedStringToString,[""]);
          return new _A_($UHC.$Base.$showsPrec,[$Show__,0,$x,$__]);});
$UHC.$Base.$show=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._1;});
$UHC.$Base.$Show__CLS74__43__0DFLUHC_2eBase_2eshowsPrec=
 new _F_(function($Show__,$__,$x)
         {var $__4=
           new _A_($UHC.$Base.$show,[$Show__,$x]);
          return new _A_($UHC.$Base.$_2b_2b,[$__4]);});
$UHC.$Base.$Show__CLS74__43__0=
 new _F_(function($Show__)
         {var $__=
           new _A_($UHC.$Base.$Show__CLS74__43__0DFLUHC_2eBase_2eshowsPrec,[$Show__]);
          var $__3=
           new _A_($UHC.$Base.$Show__CLS74__43__0DFLUHC_2eBase_2eshowList,[$Show__]);
          var $__4=
           new _A_($UHC.$Base.$Show__CLS74__43__0DFLUHC_2eBase_2eshow,[$Show__]);
          var $Show__5=
           {_tag_:0,_1:$__4,_2:$__3,_3:$__};
          return $Show__5;});
$Prolog.$__28__0__0NEW802UNQ394EVLRDC=
 new _F_(function($__)
         {var $Show__=
           _e_(new _A_($UHC.$Base.$Show__CLS74__43__0,[$__]));
          var $__6=
           {_tag_:0,_1:$Show__._1,_2:$Show__._2,_3:$Prolog.$__28__0__0DFLUHC_2eBase_2eshowsPrec};
          return $__6;});
$Prolog.$__28__0__0NEW800UNQ393RDC=
 new _F_(function($__)
         {var $__2=
           new _A_($Prolog.$__28__0__0NEW802UNQ394EVLRDC,[$__]);
          return $__2;});
$Prolog.$__28__0__0UNQ393RDC=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$__28__0__0NEW800UNQ393RDC,[$Prolog.$__28__0__0UNQ393RDC]);}),[]);
$Prolog.$__28__0__0=
 new _A_(new _F_(function()
                 {return $Prolog.$__28__0__0UNQ393RDC;}),[]);
$JCU.$__42__4079__2__0=
 new _A_(new _F_(function()
                 {return new _A_($Data.$Tree.$__40__0__0,[$Prolog.$__28__0__0]);}),[]);
$UHC.$Base.$__78__10324__0=
 new _F_(function($_24uv__1)
         {var $_24x=
           _e_($_24uv__1);
          var $_24l__1=
           _e_($_24x[0]);
          var $__swJSW261__0;
          switch($_24l__1._tag_)
           {case 0:
             var $_24l__18=
              _e_(new _A_($UHC.$Base.$primEqChar,[$_24l__1._1,84]));
             var $__swJSW262__0;
             switch($_24l__18._tag_)
              {case 0:
                $__swJSW262__0=
                 {_tag_:1};
                break;
               case 1:
                var $_24l__29=
                 _e_($_24l__1._2);
                var $__swJSW263__0;
                switch($_24l__29._tag_)
                 {case 0:
                   var $_24l__212=
                    _e_(new _A_($UHC.$Base.$primEqChar,[$_24l__29._1,114]));
                   var $__swJSW264__0;
                   switch($_24l__212._tag_)
                    {case 0:
                      $__swJSW264__0=
                       {_tag_:1};
                      break;
                     case 1:
                      var $_24l__313=
                       _e_($_24l__29._2);
                      var $__swJSW265__0;
                      switch($_24l__313._tag_)
                       {case 0:
                         var $_24l__316=
                          _e_(new _A_($UHC.$Base.$primEqChar,[$_24l__313._1,117]));
                         var $__swJSW266__0;
                         switch($_24l__316._tag_)
                          {case 0:
                            $__swJSW266__0=
                             {_tag_:1};
                            break;
                           case 1:
                            var $_24l__417=
                             _e_($_24l__313._2);
                            var $__swJSW267__0;
                            switch($_24l__417._tag_)
                             {case 0:
                               var $_24l__420=
                                _e_(new _A_($UHC.$Base.$primEqChar,[$_24l__417._1,101]));
                               var $__swJSW268__0;
                               switch($_24l__420._tag_)
                                {case 0:
                                  $__swJSW268__0=
                                   {_tag_:1};
                                  break;
                                 case 1:
                                  var $_24l__521=
                                   _e_($_24l__417._2);
                                  var $__swJSW269__0;
                                  switch($_24l__521._tag_)
                                   {case 0:
                                     $__swJSW269__0=
                                      {_tag_:1};
                                     break;
                                    case 1:
                                     var $__=
                                      [{_tag_:1},$_24x[1]];
                                     var $__25=
                                      {_tag_:0,_1:$__,_2:{_tag_:1}};
                                     $__swJSW269__0=
                                      $__25;
                                     break;}
                                  $__swJSW268__0=
                                   $__swJSW269__0;
                                  break;}
                               $__swJSW267__0=
                                $__swJSW268__0;
                               break;
                              case 1:
                               $__swJSW267__0=
                                {_tag_:1};
                               break;}
                            $__swJSW266__0=
                             $__swJSW267__0;
                            break;}
                         $__swJSW265__0=
                          $__swJSW266__0;
                         break;
                        case 1:
                         $__swJSW265__0=
                          {_tag_:1};
                         break;}
                      $__swJSW264__0=
                       $__swJSW265__0;
                      break;}
                   $__swJSW263__0=
                    $__swJSW264__0;
                   break;
                  case 1:
                   $__swJSW263__0=
                    {_tag_:1};
                   break;}
                $__swJSW262__0=
                 $__swJSW263__0;
                break;}
             $__swJSW261__0=
              $__swJSW262__0;
             break;
            case 1:
             $__swJSW261__0=
              {_tag_:1};
             break;}
          return $__swJSW261__0;});
$UHC.$Base.$__78__10320__0=
 new _F_(function($r)
         {var $__=
           new _A_($UHC.$Base.$lex,[$r]);
          return new _A_($UHC.$Base.$concatMap,[$UHC.$Base.$__78__10324__0,$__]);});
$UHC.$Base.$__78__10274__0=
 new _F_(function($_24uv__1)
         {var $_24x=
           _e_($_24uv__1);
          var $_24l__1=
           _e_($_24x[0]);
          var $__swJSW271__0;
          switch($_24l__1._tag_)
           {case 0:
             var $_24l__18=
              _e_(new _A_($UHC.$Base.$primEqChar,[$_24l__1._1,70]));
             var $__swJSW272__0;
             switch($_24l__18._tag_)
              {case 0:
                $__swJSW272__0=
                 {_tag_:1};
                break;
               case 1:
                var $_24l__29=
                 _e_($_24l__1._2);
                var $__swJSW273__0;
                switch($_24l__29._tag_)
                 {case 0:
                   var $_24l__212=
                    _e_(new _A_($UHC.$Base.$primEqChar,[$_24l__29._1,97]));
                   var $__swJSW274__0;
                   switch($_24l__212._tag_)
                    {case 0:
                      $__swJSW274__0=
                       {_tag_:1};
                      break;
                     case 1:
                      var $_24l__313=
                       _e_($_24l__29._2);
                      var $__swJSW275__0;
                      switch($_24l__313._tag_)
                       {case 0:
                         var $_24l__316=
                          _e_(new _A_($UHC.$Base.$primEqChar,[$_24l__313._1,108]));
                         var $__swJSW276__0;
                         switch($_24l__316._tag_)
                          {case 0:
                            $__swJSW276__0=
                             {_tag_:1};
                            break;
                           case 1:
                            var $_24l__417=
                             _e_($_24l__313._2);
                            var $__swJSW277__0;
                            switch($_24l__417._tag_)
                             {case 0:
                               var $_24l__420=
                                _e_(new _A_($UHC.$Base.$primEqChar,[$_24l__417._1,115]));
                               var $__swJSW278__0;
                               switch($_24l__420._tag_)
                                {case 0:
                                  $__swJSW278__0=
                                   {_tag_:1};
                                  break;
                                 case 1:
                                  var $_24l__521=
                                   _e_($_24l__417._2);
                                  var $__swJSW279__0;
                                  switch($_24l__521._tag_)
                                   {case 0:
                                     var $_24l__524=
                                      _e_(new _A_($UHC.$Base.$primEqChar,[$_24l__521._1,101]));
                                     var $__swJSW280__0;
                                     switch($_24l__524._tag_)
                                      {case 0:
                                        $__swJSW280__0=
                                         {_tag_:1};
                                        break;
                                       case 1:
                                        var $_24l__625=
                                         _e_($_24l__521._2);
                                        var $__swJSW281__0;
                                        switch($_24l__625._tag_)
                                         {case 0:
                                           $__swJSW281__0=
                                            {_tag_:1};
                                           break;
                                          case 1:
                                           var $__=
                                            [{_tag_:0},$_24x[1]];
                                           var $__29=
                                            {_tag_:0,_1:$__,_2:{_tag_:1}};
                                           $__swJSW281__0=
                                            $__29;
                                           break;}
                                        $__swJSW280__0=
                                         $__swJSW281__0;
                                        break;}
                                     $__swJSW279__0=
                                      $__swJSW280__0;
                                     break;
                                    case 1:
                                     $__swJSW279__0=
                                      {_tag_:1};
                                     break;}
                                  $__swJSW278__0=
                                   $__swJSW279__0;
                                  break;}
                               $__swJSW277__0=
                                $__swJSW278__0;
                               break;
                              case 1:
                               $__swJSW277__0=
                                {_tag_:1};
                               break;}
                            $__swJSW276__0=
                             $__swJSW277__0;
                            break;}
                         $__swJSW275__0=
                          $__swJSW276__0;
                         break;
                        case 1:
                         $__swJSW275__0=
                          {_tag_:1};
                         break;}
                      $__swJSW274__0=
                       $__swJSW275__0;
                      break;}
                   $__swJSW273__0=
                    $__swJSW274__0;
                   break;
                  case 1:
                   $__swJSW273__0=
                    {_tag_:1};
                   break;}
                $__swJSW272__0=
                 $__swJSW273__0;
                break;}
             $__swJSW271__0=
              $__swJSW272__0;
             break;
            case 1:
             $__swJSW271__0=
              {_tag_:1};
             break;}
          return $__swJSW271__0;});
$UHC.$Base.$__78__10270__0=
 new _F_(function($r)
         {var $__=
           new _A_($UHC.$Base.$lex,[$r]);
          return new _A_($UHC.$Base.$concatMap,[$UHC.$Base.$__78__10274__0,$__]);});
$UHC.$Base.$__74__51__0DFLUHC_2eBase_2ereadsPrec=
 new _F_(function($d,$r)
         {var $__=
           new _A_($UHC.$Base.$primGtInt,[$d,10]);
          var $__4=
           new _A_($UHC.$Base.$readParen,[$__,$UHC.$Base.$__78__10320__0,$r]);
          var $__5=
           new _A_($UHC.$Base.$primGtInt,[$d,10]);
          var $__6=
           new _A_($UHC.$Base.$readParen,[$__5,$UHC.$Base.$__78__10270__0,$r]);
          return new _A_($UHC.$Base.$_2b_2b,[$__6,$__4]);});
$UHC.$Base.$_24okUNQ8497=
 new _F_(function($_24x)
         {return new _A_($UHC.$Base.$_3a,[$_24x,$UHC.$Base.$_5b_5d]);});
$UHC.$Base.$_24okUNQ8433=
 new _F_(function($_24x)
         {var $__=
           _e_($_24x);
          var $__5=
           _e_($__[0]);
          var $__swJSW283__0;
          switch($__5._tag_)
           {case 0:
             var $__8=
              _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,93,$__5._1]));
             var $__swJSW284__0;
             switch($__8._tag_)
              {case 0:
                $__swJSW284__0=
                 $UHC.$Base.$_5b_5d;
                break;
               case 1:
                var $__9=
                 _e_($__5._2);
                var $__swJSW285__0;
                switch($__9._tag_)
                 {case 0:
                   $__swJSW285__0=
                    $UHC.$Base.$_5b_5d;
                   break;
                  case 1:
                   var $__12=
                    [$UHC.$Base.$_5b_5d,$__[1]];
                   var $__13=
                    new _A_($UHC.$Base.$_3a,[$__12,$UHC.$Base.$_5b_5d]);
                   $__swJSW285__0=
                    $__13;
                   break;}
                $__swJSW284__0=
                 $__swJSW285__0;
                break;}
             $__swJSW283__0=
              $__swJSW284__0;
             break;
            case 1:
             $__swJSW283__0=
              $UHC.$Base.$_5b_5d;
             break;}
          return $__swJSW283__0;});
$UHC.$Base.$__78__10181NEW5156=
 new _F_(function($s)
         {var $__=
           new _A_($UHC.$Base.$lex,[$s]);
          return new _A_($UHC.$Base.$concatMap,[$UHC.$Base.$_24okUNQ8433,$__]);});
$UHC.$Base.$_24okUNQ8464=
 new _F_(function($x,$_24x)
         {var $__=
           _e_($_24x);
          var $__6=
           new _A_($UHC.$Base.$_3a,[$x,$__[0]]);
          var $__7=
           [$__6,$__[1]];
          var $__8=
           new _A_($UHC.$Base.$_3a,[$__7,$UHC.$Base.$_5b_5d]);
          return $__8;});
$UHC.$Base.$_24okUNQ8368=
 new _F_(function($_24x)
         {var $__=
           _e_($_24x);
          var $__5=
           _e_($__[0]);
          var $__swJSW288__0;
          switch($__5._tag_)
           {case 0:
             var $__8=
              _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,93,$__5._1]));
             var $__swJSW289__0;
             switch($__8._tag_)
              {case 0:
                $__swJSW289__0=
                 $UHC.$Base.$_5b_5d;
                break;
               case 1:
                var $__9=
                 _e_($__5._2);
                var $__swJSW290__0;
                switch($__9._tag_)
                 {case 0:
                   $__swJSW290__0=
                    $UHC.$Base.$_5b_5d;
                   break;
                  case 1:
                   var $__12=
                    [$UHC.$Base.$_5b_5d,$__[1]];
                   var $__13=
                    new _A_($UHC.$Base.$_3a,[$__12,$UHC.$Base.$_5b_5d]);
                   $__swJSW290__0=
                    $__13;
                   break;}
                $__swJSW289__0=
                 $__swJSW290__0;
                break;}
             $__swJSW288__0=
              $__swJSW289__0;
             break;
            case 1:
             $__swJSW288__0=
              $UHC.$Base.$_5b_5d;
             break;}
          return $__swJSW288__0;});
$UHC.$Base.$__78__10115NEW5133=
 new _F_(function($s)
         {var $__=
           new _A_($UHC.$Base.$lex,[$s]);
          return new _A_($UHC.$Base.$concatMap,[$UHC.$Base.$_24okUNQ8368,$__]);});
$UHC.$Base.$_24okUNQ8419=
 new _F_(function($x,$_24x)
         {var $__=
           _e_($_24x);
          var $__6=
           new _A_($UHC.$Base.$_3a,[$x,$__[0]]);
          var $__7=
           [$__6,$__[1]];
          var $__8=
           new _A_($UHC.$Base.$_3a,[$__7,$UHC.$Base.$_5b_5d]);
          return $__8;});
$UHC.$Base.$_24okUNQ8408=
 new _F_(function($Read__,$_24x)
         {var $__=
           _e_($_24x);
          var $__6=
           new _A_($UHC.$Base.$readl_27UNQ8364,[$Read__,$__[1]]);
          var $__7=
           new _A_($UHC.$Base.$_24okUNQ8419,[$__[0]]);
          return new _A_($UHC.$Base.$concatMap,[$__7,$__6]);});
$UHC.$Base.$_24okUNQ8389=
 new _F_(function($Read__,$_24x)
         {var $__=
           _e_($_24x);
          var $__6=
           _e_($__[0]);
          var $__swJSW294__0;
          switch($__6._tag_)
           {case 0:
             var $__9=
              _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,44,$__6._1]));
             var $__swJSW295__0;
             switch($__9._tag_)
              {case 0:
                $__swJSW295__0=
                 $UHC.$Base.$_5b_5d;
                break;
               case 1:
                var $__10=
                 _e_($__6._2);
                var $__swJSW296__0;
                switch($__10._tag_)
                 {case 0:
                   $__swJSW296__0=
                    $UHC.$Base.$_5b_5d;
                   break;
                  case 1:
                   var $__13=
                    new _A_($UHC.$Base.$reads,[$Read__,$__[1]]);
                   var $__14=
                    new _A_($UHC.$Base.$_24okUNQ8408,[$Read__]);
                   $__swJSW296__0=
                    new _A_($UHC.$Base.$concatMap,[$__14,$__13]);
                   break;}
                $__swJSW295__0=
                 $__swJSW296__0;
                break;}
             $__swJSW294__0=
              $__swJSW295__0;
             break;
            case 1:
             $__swJSW294__0=
              $UHC.$Base.$_5b_5d;
             break;}
          return $__swJSW294__0;});
$UHC.$Base.$__78__10136NEW5115=
 new _F_(function($Read__,$s)
         {var $__=
           new _A_($UHC.$Base.$lex,[$s]);
          var $__4=
           new _A_($UHC.$Base.$_24okUNQ8389,[$Read__]);
          return new _A_($UHC.$Base.$concatMap,[$__4,$__]);});
$UHC.$Base.$readl_27UNQ8364=
 new _F_(function($Read__,$s)
         {var $__=
           new _A_($UHC.$Base.$__78__10136NEW5115,[$Read__,$s]);
          var $__4=
           new _A_($UHC.$Base.$__78__10115NEW5133,[$s]);
          return new _A_($UHC.$Base.$_2b_2b,[$__4,$__]);});
$UHC.$Base.$_24okUNQ8453=
 new _F_(function($Read__,$_24x)
         {var $__=
           _e_($_24x);
          var $__6=
           new _A_($UHC.$Base.$readl_27UNQ8364,[$Read__,$__[1]]);
          var $__7=
           new _A_($UHC.$Base.$_24okUNQ8464,[$__[0]]);
          return new _A_($UHC.$Base.$concatMap,[$__7,$__6]);});
$UHC.$Base.$readsPrec=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._2;});
$UHC.$Base.$reads=
 new _F_(function($__)
         {return new _A_($UHC.$Base.$readsPrec,[$__,0]);});
$UHC.$Base.$__78__10202NEW5144=
 new _F_(function($Read__,$s)
         {var $__=
           new _A_($UHC.$Base.$reads,[$Read__,$s]);
          var $__4=
           new _A_($UHC.$Base.$_24okUNQ8453,[$Read__]);
          return new _A_($UHC.$Base.$concatMap,[$__4,$__]);});
$UHC.$Base.$readlUNQ8365=
 new _F_(function($Read__,$s)
         {var $__=
           new _A_($UHC.$Base.$__78__10202NEW5144,[$Read__,$s]);
          var $__4=
           new _A_($UHC.$Base.$__78__10181NEW5156,[$s]);
          return new _A_($UHC.$Base.$_2b_2b,[$__4,$__]);});
$UHC.$Base.$_24okUNQ8478=
 new _F_(function($Read__,$_24x)
         {var $__=
           _e_($_24x);
          var $__6=
           _e_($__[0]);
          var $__swJSW300__0;
          switch($__6._tag_)
           {case 0:
             var $__9=
              _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,91,$__6._1]));
             var $__swJSW301__0;
             switch($__9._tag_)
              {case 0:
                $__swJSW301__0=
                 $UHC.$Base.$_5b_5d;
                break;
               case 1:
                var $__10=
                 _e_($__6._2);
                var $__swJSW302__0;
                switch($__10._tag_)
                 {case 0:
                   $__swJSW302__0=
                    $UHC.$Base.$_5b_5d;
                   break;
                  case 1:
                   var $__13=
                    new _A_($UHC.$Base.$readlUNQ8365,[$Read__,$__[1]]);
                   $__swJSW302__0=
                    new _A_($UHC.$Base.$concatMap,[$UHC.$Base.$_24okUNQ8497,$__13]);
                   break;}
                $__swJSW301__0=
                 $__swJSW302__0;
                break;}
             $__swJSW300__0=
              $__swJSW301__0;
             break;
            case 1:
             $__swJSW300__0=
              $UHC.$Base.$_5b_5d;
             break;}
          return $__swJSW300__0;});
$UHC.$Base.$__78__10227__0=
 new _F_(function($Read__,$r)
         {var $__=
           new _A_($UHC.$Base.$lex,[$r]);
          var $__4=
           new _A_($UHC.$Base.$_24okUNQ8478,[$Read__]);
          return new _A_($UHC.$Base.$concatMap,[$__4,$__]);});
$UHC.$Base.$_24okUNQ8142=
 new _F_(function($x,$_24x)
         {var $__=
           _e_($_24x);
          var $__6=
           _e_($__[0]);
          var $__swJSW304__0;
          switch($__6._tag_)
           {case 0:
             var $__9=
              _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,41,$__6._1]));
             var $__swJSW305__0;
             switch($__9._tag_)
              {case 0:
                $__swJSW305__0=
                 $UHC.$Base.$_5b_5d;
                break;
               case 1:
                var $__10=
                 _e_($__6._2);
                var $__swJSW306__0;
                switch($__10._tag_)
                 {case 0:
                   $__swJSW306__0=
                    $UHC.$Base.$_5b_5d;
                   break;
                  case 1:
                   var $__13=
                    [$x,$__[1]];
                   var $__14=
                    new _A_($UHC.$Base.$_3a,[$__13,$UHC.$Base.$_5b_5d]);
                   $__swJSW306__0=
                    $__14;
                   break;}
                $__swJSW305__0=
                 $__swJSW306__0;
                break;}
             $__swJSW304__0=
              $__swJSW305__0;
             break;
            case 1:
             $__swJSW304__0=
              $UHC.$Base.$_5b_5d;
             break;}
          return $__swJSW304__0;});
$UHC.$Base.$_24okUNQ8130=
 new _F_(function($_24x)
         {var $__=
           _e_($_24x);
          var $__5=
           new _A_($UHC.$Base.$lex,[$__[1]]);
          var $__6=
           new _A_($UHC.$Base.$_24okUNQ8142,[$__[0]]);
          return new _A_($UHC.$Base.$concatMap,[$__6,$__5]);});
$UHC.$Base.$_24okUNQ8111=
 new _F_(function($g,$_24x)
         {var $__=
           _e_($_24x);
          var $__6=
           _e_($__[0]);
          var $__swJSW309__0;
          switch($__6._tag_)
           {case 0:
             var $__9=
              _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,40,$__6._1]));
             var $__swJSW310__0;
             switch($__9._tag_)
              {case 0:
                $__swJSW310__0=
                 $UHC.$Base.$_5b_5d;
                break;
               case 1:
                var $__10=
                 _e_($__6._2);
                var $__swJSW311__0;
                switch($__10._tag_)
                 {case 0:
                   $__swJSW311__0=
                    $UHC.$Base.$_5b_5d;
                   break;
                  case 1:
                   var $__13=
                    new _A_($UHC.$Base.$optionalUNQ8106,[$g,$__[1]]);
                   $__swJSW311__0=
                    new _A_($UHC.$Base.$concatMap,[$UHC.$Base.$_24okUNQ8130,$__13]);
                   break;}
                $__swJSW310__0=
                 $__swJSW311__0;
                break;}
             $__swJSW309__0=
              $__swJSW310__0;
             break;
            case 1:
             $__swJSW309__0=
              $UHC.$Base.$_5b_5d;
             break;}
          return $__swJSW309__0;});
$UHC.$Base.$isSpace=
 new _F_(function($c)
         {var $__=
           new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,$c,160]);
          var $__3=
           new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,$c,11]);
          var $__4=
           new _A_($UHC.$Base.$_7c_7c,[$__3,$__]);
          var $__5=
           new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,$c,12]);
          var $__6=
           new _A_($UHC.$Base.$_7c_7c,[$__5,$__4]);
          var $__7=
           new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,$c,13]);
          var $__8=
           new _A_($UHC.$Base.$_7c_7c,[$__7,$__6]);
          var $__9=
           new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,$c,10]);
          var $__10=
           new _A_($UHC.$Base.$_7c_7c,[$__9,$__8]);
          var $__11=
           new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,$c,9]);
          var $__12=
           new _A_($UHC.$Base.$_7c_7c,[$__11,$__10]);
          var $__13=
           new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,$c,32]);
          return new _A_($UHC.$Base.$_7c_7c,[$__13,$__12]);});
$UHC.$Base.$pNEW1245UNQ3432CCN=
 new _F_(function($x1,$x2)
         {var $x23=
           _e_($x2);
          var $__swJSW312__0;
          switch($x23._tag_)
           {case 0:
             var $__=
              new _A_($x1,[$x23._1]);
             var $__7=
              _e_($__);
             var $__swJSW313__0;
             switch($__7._tag_)
              {case 0:
                var $__8=
                 _e_($UHC.$Base.$otherwise);
                var $__swJSW314__0;
                switch($__8._tag_)
                 {case 0:
                   $__swJSW314__0=
                    $UHC.$Base.$undefined;
                   break;
                  case 1:
                   $__swJSW314__0=
                    $x23;
                   break;}
                $__swJSW313__0=
                 $__swJSW314__0;
                break;
               case 1:
                var $__9=
                 new _A_($UHC.$Base.$dropWhile,[$x1,$x23._2]);
                $__swJSW313__0=
                 $__9;
                break;}
             $__swJSW312__0=
              $__swJSW313__0;
             break;
            case 1:
             $__swJSW312__0=
              $UHC.$Base.$undefined;
             break;}
          return $__swJSW312__0;});
$UHC.$Base.$dropWhile=
 new _F_(function($x1,$x2)
         {var $p=
           new _A_($UHC.$Base.$pNEW1245UNQ3432CCN,[$x1,$x2]);
          var $x24=
           _e_($x2);
          var $__swJSW315__0;
          switch($x24._tag_)
           {case 0:
             $__swJSW315__0=
              $p;
             break;
            case 1:
             $__swJSW315__0=
              $UHC.$Base.$_5b_5d;
             break;}
          return $__swJSW315__0;});
$UHC.$Base.$isAlphaNum=
 new _F_(function($c)
         {var $__=
           new _A_($UHC.$Base.$isDigit,[$c]);
          var $__3=
           new _A_($UHC.$Base.$isAlpha,[$c]);
          return new _A_($UHC.$Base.$_7c_7c,[$__3,$__]);});
$UHC.$Base.$isLower=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return primCharIsLower($__2);});
$UHC.$Base.$isAlpha=
 new _F_(function($c)
         {var $__=
           new _A_($UHC.$Base.$isLower,[$c]);
          var $__3=
           new _A_($UHC.$Base.$isUpper,[$c]);
          return new _A_($UHC.$Base.$_7c_7c,[$__3,$__]);});
$UHC.$Base.$zipWith=
 new _F_(function($x1,$x2,$x3)
         {var $x24=
           _e_($x2);
          var $__swJSW316__0;
          switch($x24._tag_)
           {case 0:
             var $x37=
              _e_($x3);
             var $__swJSW317__0;
             switch($x37._tag_)
              {case 0:
                var $__=
                 new _A_($UHC.$Base.$zipWith,[$x1,$x24._2,$x37._2]);
                var $__11=
                 new _A_($x1,[$x24._1,$x37._1]);
                var $__12=
                 new _A_($UHC.$Base.$_3a,[$__11,$__]);
                $__swJSW317__0=
                 $__12;
                break;
               case 1:
                $__swJSW317__0=
                 $UHC.$Base.$_5b_5d;
                break;}
             $__swJSW316__0=
              $__swJSW317__0;
             break;
            case 1:
             $__swJSW316__0=
              $UHC.$Base.$_5b_5d;
             break;}
          return $__swJSW316__0;});
$UHC.$Base.$__78__3116__0=
 new _F_(function($a,$b)
         {return [$a,$b];});
$UHC.$Base.$zip=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$zipWith,[$UHC.$Base.$__78__3116__0]);}),[]);
$UHC.$Base.$__78__9318=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["ENQ"]);}),[]);
$UHC.$Base.$__78__9324=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["BEL"]);}),[]);
$UHC.$Base.$__78__9322=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9324,$UHC.$Base.$_5b_5d]);}),[]);
$UHC.$Base.$__78__9321=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["ACK"]);}),[]);
$UHC.$Base.$__78__9319=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9321,$UHC.$Base.$__78__9322]);}),[]);
$UHC.$Base.$__78__9316=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9318,$UHC.$Base.$__78__9319]);}),[]);
$UHC.$Base.$__78__9315=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["EOT"]);}),[]);
$UHC.$Base.$__78__9313=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9315,$UHC.$Base.$__78__9316]);}),[]);
$UHC.$Base.$__78__9363=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["DC2"]);}),[]);
$UHC.$Base.$__78__9366=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["DC3"]);}),[]);
$UHC.$Base.$__78__9364=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9366,$UHC.$Base.$_5b_5d]);}),[]);
$UHC.$Base.$__78__9361=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9363,$UHC.$Base.$__78__9364]);}),[]);
$UHC.$Base.$__78__9360=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["DC1"]);}),[]);
$UHC.$Base.$__78__9358=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9360,$UHC.$Base.$__78__9361]);}),[]);
$UHC.$Base.$__78__9357=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["DLE"]);}),[]);
$UHC.$Base.$__78__9355=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9357,$UHC.$Base.$__78__9358]);}),[]);
$UHC.$Base.$__78__9399=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["FS"]);}),[]);
$UHC.$Base.$__78__9402=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["GS"]);}),[]);
$UHC.$Base.$__78__9408=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["US"]);}),[]);
$UHC.$Base.$__78__9406=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9408,$UHC.$Base.$_5b_5d]);}),[]);
$UHC.$Base.$__78__9405=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["RS"]);}),[]);
$UHC.$Base.$__78__9403=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9405,$UHC.$Base.$__78__9406]);}),[]);
$UHC.$Base.$__78__9400=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9402,$UHC.$Base.$__78__9403]);}),[]);
$UHC.$Base.$__78__9397=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9399,$UHC.$Base.$__78__9400]);}),[]);
$UHC.$Base.$__78__9411=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["SP"]);}),[]);
$UHC.$Base.$__78__9409=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9411,$UHC.$Base.$_5b_5d]);}),[]);
$UHC.$Base.$__78__9395=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_2b_2b,[$UHC.$Base.$__78__9397,$UHC.$Base.$__78__9409]);}),[]);
$UHC.$Base.$__78__9385=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["CAN"]);}),[]);
$UHC.$Base.$__78__9394=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["ESC"]);}),[]);
$UHC.$Base.$__78__9392=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9394,$UHC.$Base.$_5b_5d]);}),[]);
$UHC.$Base.$__78__9391=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["SUB"]);}),[]);
$UHC.$Base.$__78__9389=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9391,$UHC.$Base.$__78__9392]);}),[]);
$UHC.$Base.$__78__9388=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["EM"]);}),[]);
$UHC.$Base.$__78__9386=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9388,$UHC.$Base.$__78__9389]);}),[]);
$UHC.$Base.$__78__9383=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9385,$UHC.$Base.$__78__9386]);}),[]);
$UHC.$Base.$__78__9381=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_2b_2b,[$UHC.$Base.$__78__9383,$UHC.$Base.$__78__9395]);}),[]);
$UHC.$Base.$__78__9371=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["DC4"]);}),[]);
$UHC.$Base.$__78__9374=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["NAK"]);}),[]);
$UHC.$Base.$__78__9377=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["SYN"]);}),[]);
$UHC.$Base.$__78__9380=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["ETB"]);}),[]);
$UHC.$Base.$__78__9378=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9380,$UHC.$Base.$_5b_5d]);}),[]);
$UHC.$Base.$__78__9375=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9377,$UHC.$Base.$__78__9378]);}),[]);
$UHC.$Base.$__78__9372=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9374,$UHC.$Base.$__78__9375]);}),[]);
$UHC.$Base.$__78__9369=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9371,$UHC.$Base.$__78__9372]);}),[]);
$UHC.$Base.$__78__9367=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_2b_2b,[$UHC.$Base.$__78__9369,$UHC.$Base.$__78__9381]);}),[]);
$UHC.$Base.$__78__9353=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_2b_2b,[$UHC.$Base.$__78__9355,$UHC.$Base.$__78__9367]);}),[]);
$UHC.$Base.$__78__9352=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["SI"]);}),[]);
$UHC.$Base.$__78__9350=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9352,$UHC.$Base.$_5b_5d]);}),[]);
$UHC.$Base.$__78__9349=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["SO"]);}),[]);
$UHC.$Base.$__78__9347=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9349,$UHC.$Base.$__78__9350]);}),[]);
$UHC.$Base.$__78__9346=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["CR"]);}),[]);
$UHC.$Base.$__78__9344=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9346,$UHC.$Base.$__78__9347]);}),[]);
$UHC.$Base.$__78__9343=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["FF"]);}),[]);
$UHC.$Base.$__78__9341=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9343,$UHC.$Base.$__78__9344]);}),[]);
$UHC.$Base.$__78__9339=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_2b_2b,[$UHC.$Base.$__78__9341,$UHC.$Base.$__78__9353]);}),[]);
$UHC.$Base.$__78__9332=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["HT"]);}),[]);
$UHC.$Base.$__78__9335=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["LF"]);}),[]);
$UHC.$Base.$__78__9338=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["VT"]);}),[]);
$UHC.$Base.$__78__9336=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9338,$UHC.$Base.$_5b_5d]);}),[]);
$UHC.$Base.$__78__9333=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9335,$UHC.$Base.$__78__9336]);}),[]);
$UHC.$Base.$__78__9330=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9332,$UHC.$Base.$__78__9333]);}),[]);
$UHC.$Base.$__78__9329=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["BS"]);}),[]);
$UHC.$Base.$__78__9327=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9329,$UHC.$Base.$__78__9330]);}),[]);
$UHC.$Base.$__78__9325=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_2b_2b,[$UHC.$Base.$__78__9327,$UHC.$Base.$__78__9339]);}),[]);
$UHC.$Base.$__78__9311=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_2b_2b,[$UHC.$Base.$__78__9313,$UHC.$Base.$__78__9325]);}),[]);
$UHC.$Base.$__78__9301=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["NUL"]);}),[]);
$UHC.$Base.$__78__9307=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["STX"]);}),[]);
$UHC.$Base.$__78__9310=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["ETX"]);}),[]);
$UHC.$Base.$__78__9308=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9310,$UHC.$Base.$_5b_5d]);}),[]);
$UHC.$Base.$__78__9305=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9307,$UHC.$Base.$__78__9308]);}),[]);
$UHC.$Base.$__78__9304=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["SOH"]);}),[]);
$UHC.$Base.$__78__9302=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9304,$UHC.$Base.$__78__9305]);}),[]);
$UHC.$Base.$__78__9299=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3a,[$UHC.$Base.$__78__9301,$UHC.$Base.$__78__9302]);}),[]);
$UHC.$Base.$__78__9297=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_2b_2b,[$UHC.$Base.$__78__9299,$UHC.$Base.$__78__9311]);}),[]);
$UHC.$Base.$enumFromTo=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._4;});
$UHC.$Base.$primDivInt=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__2);
          return primDivInt($__3,$__4);});
$UHC.$Base.$primAddInt=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__2);
          return primAddInt($__3,$__4);});
$UHC.$Base.$primSubInt=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__2);
          return primSubInt($__3,$__4);});
$UHC.$Base.$__78__3041__0=
 new _F_(function($__,$_24x__75__36__0)
         {var $__3=
           new _A_($UHC.$Base.$packedStringToInteger,["1"]);
          var $__4=
           new _A_($UHC.$Base.$fromInteger,[$__,$__3]);
          return new _A_($UHC.$Base.$_2b,[$__,$_24x__75__36__0,$__4]);});
$UHC.$Base.$numericEnumFrom=
 new _F_(function($__)
         {var $__2=
           new _A_($UHC.$Base.$__78__3041__0,[$__]);
          return new _A_($UHC.$Base.$iterate_27,[$__2]);});
$UHC.$Base.$primNegInt=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return primNegInt($__2);});
$UHC.$Base.$primIntegerToInt=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return primIntegerToInt($__2);});
$UHC.$Base.$subtract=
 new _F_(function($__)
         {var $__2=
           new _A_($UHC.$Base.$_2d,[$__]);
          return new _A_($UHC.$Base.$flip,[$__2]);});
$UHC.$Base.$__76__26391__2__0NEW3895UNQ6972=
 new _F_(function($__)
         {var $Eq__=
           _e_($__);
          return $Eq__._4;});
$UHC.$Base.$__78__7922__0=
 new _F_(function($__,$__2,$__3,$x)
         {var $__5=
           new _A_($UHC.$Base.$minBound,[$__2]);
          var $__6=
           new _A_($UHC.$Base.$_3d_3d,[$__3,$x,$__5]);
          var $__7=
           _e_($__6);
          var $__swJSW320__0;
          switch($__7._tag_)
           {case 0:
             var $__8=
              _e_($UHC.$Base.$otherwise);
             var $__swJSW321__0;
             switch($__8._tag_)
              {case 0:
                var $__9=
                 new _A_($UHC.$Base.$packedStringToString,["FAIL 75_22_0"]);
                var $__10=
                 new _A_($UHC.$Base.$error,[$__9]);
                $__swJSW321__0=
                 $__10;
                break;
               case 1:
                var $__11=
                 new _A_($UHC.$Base.$packedStringToInteger,["1"]);
                var $__12=
                 new _A_($UHC.$Base.$fromInteger,[$__,$__11]);
                var $__13=
                 new _A_($UHC.$Base.$_2d,[$__,$x,$__12]);
                $__swJSW321__0=
                 $__13;
                break;}
             $__swJSW320__0=
              $__swJSW321__0;
             break;
            case 1:
             var $__14=
              new _A_($UHC.$Base.$packedStringToString,["pred: applied to minBound"]);
             var $__15=
              new _A_($UHC.$Base.$error,[$__14]);
             $__swJSW320__0=
              $__15;
             break;}
          return $__swJSW320__0;});
$UHC.$Base.$boundedPred=
 new _F_(function($__,$__2,$__3)
         {var $__4=
           new _A_($UHC.$Base.$__76__26391__2__0NEW3895UNQ6972,[$__]);
          return new _A_($UHC.$Base.$__78__7922__0,[$__,$__2,$__4]);});
$UHC.$Base.$enumFrom=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._1;});
$UHC.$Base.$toInt=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._9;});
$UHC.$Base.$primRemInt=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__2);
          return primRemInt($__3,$__4);});
$UHC.$Base.$__76__20310__2__0NEW3938UNQ5199=
 new _F_(function($__)
         {var $Num__=
           _e_($__);
          return $Num__._1;});
$UHC.$Base.$__76__17006__2__95NEW3935UNQ5203=
 new _F_(function($__)
         {var $Real__=
           _e_($__);
          return $Real__._2;});
$UHC.$Base.$__76__17006__2__101NEW3911UNQ5063=
 new _F_(function($__)
         {var $Real__=
           _e_($__);
          return $Real__._2;});
$UHC.$Base.$__76__19701__2__0NEW3914UNQ5057=
 new _F_(function($__)
         {var $Num__=
           _e_($__);
          return $Num__._1;});
$UHC.$Base.$_3a_25=
 new _F_(function($x1,$x2)
         {return {_tag_:0,_1:$x1,_2:$x2};});
$UHC.$Base.$rem=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._8;});
$UHC.$Base.$gcd_27UNQ5156=
 new _F_(function($__,$__2,$__3,$x1,$x2)
         {var $__6=
           new _A_($UHC.$Base.$rem,[$__,$x1,$x2]);
          var $__7=
           new _A_($UHC.$Base.$gcd_27UNQ5156,[$__,$__2,$__3,$x2,$__6]);
          var $__8=
           new _A_($UHC.$Base.$packedStringToInteger,["0"]);
          var $__9=
           new _A_($UHC.$Base.$fromInteger,[$__3,$__8]);
          var $x210=
           _e_(new _A_($UHC.$Base.$_3d_3d,[$__2,$__9,$x2]));
          var $__swJSW329__0;
          switch($x210._tag_)
           {case 0:
             $__swJSW329__0=
              $__7;
             break;
            case 1:
             $__swJSW329__0=
              $x1;
             break;}
          return $__swJSW329__0;});
$UHC.$Base.$__76__19858__0NEW2313UNQ5153CCN=
 new _F_(function($__,$__2,$__3,$x1,$x2)
         {var $__6=
           new _A_($UHC.$Base.$abs,[$__,$x2]);
          var $__7=
           new _A_($UHC.$Base.$abs,[$__,$x1]);
          return new _A_($UHC.$Base.$gcd_27UNQ5156,[$__3,$__2,$__,$__7,$__6]);});
$UHC.$Base.$__78__4950__0=
 new _F_(function($__,$__2,$__3,$x1,$x2)
         {var $__6=
           new _A_($UHC.$Base.$__76__19858__0NEW2313UNQ5153CCN,[$__,$__2,$__3,$x1,$x2]);
          var $__7=
           new _A_($UHC.$Base.$packedStringToInteger,["0"]);
          var $__8=
           new _A_($UHC.$Base.$fromInteger,[$__,$__7]);
          var $x19=
           _e_(new _A_($UHC.$Base.$_3d_3d,[$__2,$__8,$x1]));
          var $__swJSW330__0;
          switch($x19._tag_)
           {case 0:
             $__swJSW330__0=
              $__6;
             break;
            case 1:
             var $__10=
              new _A_($UHC.$Base.$packedStringToInteger,["0"]);
             var $__11=
              new _A_($UHC.$Base.$fromInteger,[$__,$__10]);
             var $x212=
              _e_(new _A_($UHC.$Base.$_3d_3d,[$__2,$__11,$x2]));
             var $__swJSW331__0;
             switch($x212._tag_)
              {case 0:
                $__swJSW331__0=
                 $__6;
                break;
               case 1:
                var $__13=
                 new _A_($UHC.$Base.$packedStringToString,["Prelude.gcd: gcd 0 0 is undefined"]);
                var $__14=
                 new _A_($UHC.$Base.$error,[$__13]);
                $__swJSW331__0=
                 $__14;
                break;}
             $__swJSW330__0=
              $__swJSW331__0;
             break;}
          return $__swJSW330__0;});
$UHC.$Base.$__76__20029__8__0NEW2306UNQ5098=
 new _F_(function($__)
         {var $Num__=
           _e_($__);
          return $Num__._1;});
$UHC.$Base.$__76__17006__2__3NEW2303UNQ5097=
 new _F_(function($__)
         {var $Real__=
           _e_($__);
          return $Real__._2;});
$UHC.$Base.$__76__20029__5__0NEW2309UNQ5099=
 new _F_(function($__)
         {var $Eq__=
           _e_($__);
          return $Eq__._4;});
$UHC.$Base.$gcd=
 new _F_(function($__)
         {var $__2=
           new _A_($UHC.$Base.$__76__17006__2__3NEW2303UNQ5097,[$__]);
          var $__3=
           new _A_($UHC.$Base.$__76__20029__8__0NEW2306UNQ5098,[$__2]);
          var $__4=
           new _A_($UHC.$Base.$__76__20029__5__0NEW2309UNQ5099,[$__3]);
          return new _A_($UHC.$Base.$__78__4950__0,[$__3,$__4,$__]);});
$UHC.$Base.$quot=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._6;});
$UHC.$Base.$__78__7955__0=
 new _F_(function($__,$__2,$__3,$x,$y)
         {var $d=
           new _A_($UHC.$Base.$gcd,[$__2,$x,$y]);
          var $__7=
           new _A_($UHC.$Base.$packedStringToInteger,["0"]);
          var $__8=
           new _A_($UHC.$Base.$fromInteger,[$__,$__7]);
          var $__9=
           new _A_($UHC.$Base.$_3d_3d,[$__3,$y,$__8]);
          var $__10=
           _e_($__9);
          var $__swJSW336__0;
          switch($__10._tag_)
           {case 0:
             var $__11=
              _e_($UHC.$Base.$otherwise);
             var $__swJSW337__0;
             switch($__11._tag_)
              {case 0:
                var $__12=
                 new _A_($UHC.$Base.$packedStringToString,["FAIL 75_444_0"]);
                var $__13=
                 new _A_($UHC.$Base.$error,[$__12]);
                $__swJSW337__0=
                 $__13;
                break;
               case 1:
                var $__14=
                 new _A_($UHC.$Base.$quot,[$__2,$y,$d]);
                var $__15=
                 new _A_($UHC.$Base.$quot,[$__2,$x,$d]);
                var $__16=
                 new _A_($UHC.$Base.$_3a_25,[$__15,$__14]);
                $__swJSW337__0=
                 $__16;
                break;}
             $__swJSW336__0=
              $__swJSW337__0;
             break;
            case 1:
             var $__17=
              new _A_($UHC.$Base.$packedStringToString,["Ratio.%: zero denominator"]);
             var $__18=
              new _A_($UHC.$Base.$error,[$__17]);
             $__swJSW336__0=
              $__18;
             break;}
          return $__swJSW336__0;});
$UHC.$Base.$__76__19691__2__0NEW3917UNQ5058=
 new _F_(function($__)
         {var $Eq__=
           _e_($__);
          return $Eq__._4;});
$UHC.$Base.$reduce=
 new _F_(function($__)
         {var $__2=
           new _A_($UHC.$Base.$__76__17006__2__101NEW3911UNQ5063,[$__]);
          var $__3=
           new _A_($UHC.$Base.$__76__19701__2__0NEW3914UNQ5057,[$__2]);
          var $__4=
           new _A_($UHC.$Base.$__76__19691__2__0NEW3917UNQ5058,[$__3]);
          return new _A_($UHC.$Base.$__78__7955__0,[$__3,$__,$__4]);});
$UHC.$Base.$_2a=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._1;});
$UHC.$Base.$abs=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._5;});
$UHC.$Base.$__78__7995__0=
 new _F_(function($__,$__2,$x,$y)
         {var $__5=
           new _A_($UHC.$Base.$abs,[$__,$y]);
          var $__6=
           new _A_($UHC.$Base.$signum,[$__,$y]);
          var $__7=
           new _A_($UHC.$Base.$_2a,[$__,$x,$__6]);
          return new _A_($UHC.$Base.$reduce,[$__2,$__7,$__5]);});
$UHC.$Base.$_25=
 new _F_(function($__)
         {var $__2=
           new _A_($UHC.$Base.$__76__17006__2__95NEW3935UNQ5203,[$__]);
          var $__3=
           new _A_($UHC.$Base.$__76__20310__2__0NEW3938UNQ5199,[$__2]);
          return new _A_($UHC.$Base.$__78__7995__0,[$__3,$__]);});
$UHC.$Base.$fromIntegral=
 new _F_(function($__,$__2)
         {var $__3=
           new _A_($UHC.$Base.$toInteger,[$__]);
          var $__4=
           new _A_($UHC.$Base.$fromInteger,[$__2]);
          return new _A_($UHC.$Base.$_2e,[$__4,$__3]);});
$UHC.$Base.$Bounded__CLS74__6__0=
 new _F_(function($Bounded__)
         {var $Bounded__2=
           {_tag_:0,_1:$UHC.$Base.$undefined,_2:$UHC.$Base.$undefined};
          return $Bounded__2;});
$UHC.$Base.$primMaxInt=
 new _A_(new _F_(function()
                 {return primMaxInt();}),[]);
$UHC.$Base.$primMinInt=
 new _A_(new _F_(function()
                 {return primMinInt();}),[]);
$UHC.$Base.$Bounded__NEW1337UNQ9657EVLDCT74__97__0RDC=
 new _F_(function($Bounded__)
         {var $Bounded__2=
           _e_(new _A_($UHC.$Base.$Bounded__CLS74__6__0,[$Bounded__]));
          var $__5=
           {_tag_:0,_1:$UHC.$Base.$primMaxInt,_2:$UHC.$Base.$primMinInt};
          return $__5;});
$UHC.$Base.$Bounded__NEW1335UNQ9656DCT74__97__0RDC=
 new _F_(function($Bounded__)
         {var $Bounded__2=
           new _A_($UHC.$Base.$Bounded__NEW1337UNQ9657EVLDCT74__97__0RDC,[$Bounded__]);
          return $Bounded__2;});
$UHC.$Base.$Bounded__UNQ9656DCT74__97__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Bounded__NEW1335UNQ9656DCT74__97__0RDC,[$UHC.$Base.$Bounded__UNQ9656DCT74__97__0RDC]);}),[]);
$UHC.$Base.$Bounded__DCT74__97__0=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$Bounded__UNQ9656DCT74__97__0RDC;}),[]);
$UHC.$Base.$quotRem=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._7;});
$UHC.$Base.$primDivModInteger=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__2);
          return primDivModInteger($__3,$__4);});
$UHC.$Base.$__78__3884__0=
 new _F_(function($__,$m,$_24x__75__26__0)
         {return new _A_($UHC.$Base.$_3c_3d,[$__,$_24x__75__26__0,$m]);});
$UHC.$Base.$boundedEnumFromTo=
 new _F_(function($__,$__2,$__3,$n,$m)
         {var $__6=
           new _A_($UHC.$Base.$boundedEnumFrom,[$__,$__2,$__3,$n]);
          var $__7=
           new _A_($UHC.$Base.$__78__3884__0,[$__,$m]);
          return new _A_($UHC.$Base.$takeWhile,[$__7,$__6]);});
$UHC.$Base.$primModInt=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__2);
          return primModInt($__3,$__4);});
$UHC.$Base.$__78__3068__0=
 new _F_(function($__,$n,$m,$_24x__75__38__0)
         {var $__5=
           new _A_($UHC.$Base.$_2d,[$__,$m,$n]);
          return new _A_($UHC.$Base.$_2b,[$__,$_24x__75__38__0,$__5]);});
$UHC.$Base.$__78__1305NEW380=
 new _F_(function($f,$x)
         {var $fx=
           new _A_($f,[$x]);
          var $fx4=
           _e_($fx);
          return new _A_($UHC.$Base.$iterate_27,[$f,$fx]);});
$UHC.$Base.$iterate_27=
 new _F_(function($f,$x)
         {var $__=
           new _A_($UHC.$Base.$__78__1305NEW380,[$f,$x]);
          return new _A_($UHC.$Base.$_3a,[$x,$__]);});
$UHC.$Base.$numericEnumFromThen=
 new _F_(function($__,$n,$m)
         {var $__4=
           new _A_($UHC.$Base.$__78__3068__0,[$__,$n,$m]);
          return new _A_($UHC.$Base.$iterate_27,[$__4,$n]);});
$UHC.$Base.$__78__7616__0=
 new _F_(function($__,$__2,$__3,$x)
         {var $__5=
           new _A_($UHC.$Base.$maxBound,[$__2]);
          var $__6=
           new _A_($UHC.$Base.$_3d_3d,[$__3,$x,$__5]);
          var $__7=
           _e_($__6);
          var $__swJSW343__0;
          switch($__7._tag_)
           {case 0:
             var $__8=
              _e_($UHC.$Base.$otherwise);
             var $__swJSW344__0;
             switch($__8._tag_)
              {case 0:
                var $__9=
                 new _A_($UHC.$Base.$packedStringToString,["FAIL 75_21_0"]);
                var $__10=
                 new _A_($UHC.$Base.$error,[$__9]);
                $__swJSW344__0=
                 $__10;
                break;
               case 1:
                var $__11=
                 new _A_($UHC.$Base.$packedStringToInteger,["1"]);
                var $__12=
                 new _A_($UHC.$Base.$fromInteger,[$__,$__11]);
                var $__13=
                 new _A_($UHC.$Base.$_2b,[$__,$x,$__12]);
                $__swJSW344__0=
                 $__13;
                break;}
             $__swJSW343__0=
              $__swJSW344__0;
             break;
            case 1:
             var $__14=
              new _A_($UHC.$Base.$packedStringToString,["succ: applied to maxBound"]);
             var $__15=
              new _A_($UHC.$Base.$error,[$__14]);
             $__swJSW343__0=
              $__15;
             break;}
          return $__swJSW343__0;});
$UHC.$Base.$__76__26534__2__0NEW3739UNQ6994=
 new _F_(function($__)
         {var $Eq__=
           _e_($__);
          return $Eq__._4;});
$UHC.$Base.$boundedSucc=
 new _F_(function($__,$__2,$__3)
         {var $__4=
           new _A_($UHC.$Base.$__76__26534__2__0NEW3739UNQ6994,[$__]);
          return new _A_($UHC.$Base.$__78__7616__0,[$__,$__2,$__4]);});
$UHC.$Base.$_3e=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._3;});
$UHC.$Base.$__78__5471__0=
 new _F_(function($__,$__2,$__3,$x)
         {var $__5=
           new _A_($UHC.$Base.$packedStringToInteger,["0"]);
          var $__6=
           new _A_($UHC.$Base.$fromInteger,[$__2,$__5]);
          var $__7=
           new _A_($UHC.$Base.$_3d_3d,[$__3,$x,$__6]);
          var $__8=
           _e_($__7);
          var $__swJSW347__0;
          switch($__8._tag_)
           {case 0:
             var $__9=
              new _A_($UHC.$Base.$packedStringToInteger,["0"]);
             var $__10=
              new _A_($UHC.$Base.$fromInteger,[$__2,$__9]);
             var $__11=
              new _A_($UHC.$Base.$_3e,[$__,$x,$__10]);
             var $__12=
              _e_($__11);
             var $__swJSW348__0;
             switch($__12._tag_)
              {case 0:
                var $__13=
                 _e_($UHC.$Base.$otherwise);
                var $__swJSW349__0;
                switch($__13._tag_)
                 {case 0:
                   var $__14=
                    new _A_($UHC.$Base.$packedStringToString,["FAIL 75_119_0"]);
                   var $__15=
                    new _A_($UHC.$Base.$error,[$__14]);
                   $__swJSW349__0=
                    $__15;
                   break;
                  case 1:
                   var $__16=
                    new _A_($UHC.$Base.$packedStringToInteger,["1"]);
                   var $__17=
                    new _A_($UHC.$Base.$fromInteger,[$__2,$__16]);
                   var $__18=
                    new _A_($UHC.$Base.$negate,[$__2,$__17]);
                   $__swJSW349__0=
                    $__18;
                   break;}
                $__swJSW348__0=
                 $__swJSW349__0;
                break;
               case 1:
                var $__19=
                 new _A_($UHC.$Base.$packedStringToInteger,["1"]);
                var $__20=
                 new _A_($UHC.$Base.$fromInteger,[$__2,$__19]);
                $__swJSW348__0=
                 $__20;
                break;}
             $__swJSW347__0=
              $__swJSW348__0;
             break;
            case 1:
             var $__21=
              new _A_($UHC.$Base.$packedStringToInteger,["0"]);
             var $__22=
              new _A_($UHC.$Base.$fromInteger,[$__2,$__21]);
             $__swJSW347__0=
              $__22;
             break;}
          return $__swJSW347__0;});
$UHC.$Base.$__76__18754__2__0NEW2564UNQ4907=
 new _F_(function($__)
         {var $Eq__=
           _e_($__);
          return $Eq__._4;});
$UHC.$Base.$signumReal=
 new _F_(function($__,$__2)
         {var $__3=
           new _A_($UHC.$Base.$__76__18754__2__0NEW2564UNQ4907,[$__2]);
          return new _A_($UHC.$Base.$__78__5471__0,[$__,$__2,$__3]);});
$UHC.$Base.$primMulInteger=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__2);
          return $__3.multiply($__4);});
$UHC.$Base.$primQuotRemInt=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__2);
          return primQuotRemInt($__3,$__4);});
$UHC.$Base.$minBound=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._2;});
$UHC.$Base.$__78__8456NEW4292=
 new _F_(function($__,$__2,$n,$m)
         {var $__5=
           new _A_($UHC.$Base.$_3c_3d,[$__,$n,$m]);
          var $__6=
           _e_($__5);
          var $__swJSW352__0;
          switch($__6._tag_)
           {case 0:
             var $__7=
              new _A_($UHC.$Base.$minBound,[$__2]);
             $__swJSW352__0=
              $__7;
             break;
            case 1:
             var $__8=
              new _A_($UHC.$Base.$maxBound,[$__2]);
             $__swJSW352__0=
              $__8;
             break;}
          return $__swJSW352__0;});
$UHC.$Base.$boundedEnumFromThen=
 new _F_(function($__,$__2,$__3,$n,$m)
         {var $__6=
           new _A_($UHC.$Base.$__78__8456NEW4292,[$__,$__2,$n,$m]);
          return new _A_($UHC.$Base.$enumFromThenTo,[$__3,$n,$m,$__6]);});
$UHC.$Base.$enumFromThen=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._2;});
$UHC.$Base.$primQuotRemInteger=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__2);
          return primQuotRemInteger($__3,$__4);});
$UHC.$Base.$primNegInteger=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return $__2.negate();});
$UHC.$Base.$primIntToInteger=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return primIntToInteger($__2);});
$UHC.$Base.$primAddInteger=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__2);
          return $__3.add($__4);});
$UHC.$Base.$negate=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._8;});
$UHC.$Base.$absReal=
 new _F_(function($__,$__2,$x)
         {var $__4=
           new _A_($UHC.$Base.$packedStringToInteger,["0"]);
          var $__5=
           new _A_($UHC.$Base.$fromInteger,[$__2,$__4]);
          var $__6=
           new _A_($UHC.$Base.$_3e_3d,[$__,$x,$__5]);
          var $__7=
           _e_($__6);
          var $__swJSW355__0;
          switch($__7._tag_)
           {case 0:
             var $__8=
              _e_($UHC.$Base.$otherwise);
             var $__swJSW356__0;
             switch($__8._tag_)
              {case 0:
                var $__9=
                 new _A_($UHC.$Base.$packedStringToString,["FAIL 75_118_0"]);
                var $__10=
                 new _A_($UHC.$Base.$error,[$__9]);
                $__swJSW356__0=
                 $__10;
                break;
               case 1:
                var $__11=
                 new _A_($UHC.$Base.$negate,[$__2,$x]);
                $__swJSW356__0=
                 $__11;
                break;}
             $__swJSW355__0=
              $__swJSW356__0;
             break;
            case 1:
             $__swJSW355__0=
              $x;
             break;}
          return $__swJSW355__0;});
$UHC.$Base.$Real__CLS74__13__0=
 new _F_(function($Real__)
         {var $Real__2=
           {_tag_:0,_1:$UHC.$Base.$undefined,_2:$UHC.$Base.$undefined,_3:$UHC.$Base.$undefined};
          return $Real__2;});
$UHC.$Base.$primMulInt=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__2);
          return primMulInt($__3,$__4);});
$UHC.$Base.$fromInteger=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._7;});
$UHC.$Base.$divMod=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._4;});
$UHC.$Base.$packedStringToInteger=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return primPackedStringToInteger($__2);});
$UHC.$Base.$maxBound=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._1;});
$UHC.$Base.$__78__3862__0=
 new _F_(function($__,$__2,$_24x__75__24__0)
         {var $__4=
           new _A_($UHC.$Base.$maxBound,[$__]);
          return new _A_($UHC.$Base.$_2f_3d,[$__2,$_24x__75__24__0,$__4]);});
$UHC.$Base.$succ=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._7;});
$UHC.$Base.$__78__3858__0=
 new _F_(function($__,$__2,$__3,$n)
         {var $__5=
           new _A_($UHC.$Base.$succ,[$__2]);
          var $__6=
           new _A_($UHC.$Base.$iterate,[$__5,$n]);
          var $__7=
           new _A_($UHC.$Base.$__78__3862__0,[$__,$__3]);
          return new _A_($UHC.$Base.$takeWhile1,[$__7,$__6]);});
$UHC.$Base.$__76__26692__2__0NEW1767UNQ7014=
 new _F_(function($__)
         {var $Eq__=
           _e_($__);
          return $Eq__._5;});
$UHC.$Base.$boundedEnumFrom=
 new _F_(function($__,$__2,$__3)
         {var $__4=
           new _A_($UHC.$Base.$__76__26692__2__0NEW1767UNQ7014,[$__]);
          return new _A_($UHC.$Base.$__78__3858__0,[$__2,$__3,$__4]);});
$UHC.$Base.$toInteger=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._10;});
$UHC.$Base.$primQuotInteger=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__2);
          return $__3.divide($__4);});
$UHC.$Base.$primModInteger=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__2);
          return primModInteger($__3,$__4);});
$UHC.$Base.$primDivInteger=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__2);
          return primDivInteger($__3,$__4);});
$UHC.$Base.$primSubInteger=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__2);
          return $__3.subtract($__4);});
$UHC.$Base.$_2b=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._2;});
$UHC.$Base.$__78__5158__0=
 new _F_(function($__,$delta,$_24x__75__33__0)
         {return new _A_($UHC.$Base.$_2b,[$__,$_24x__75__33__0,$delta]);});
$UHC.$Base.$__78__5181__0=
 new _F_(function($__,$__2,$m,$delta,$_24x__75__30__0)
         {var $__6=
           new _A_($UHC.$Base.$_2d,[$__2,$m,$delta]);
          return new _A_($UHC.$Base.$_3e_3d,[$__,$_24x__75__30__0,$__6]);});
$UHC.$Base.$iterate=
 new _F_(function($f,$x)
         {var $__=
           new _A_($f,[$x]);
          var $__4=
           new _A_($UHC.$Base.$iterate,[$f,$__]);
          return new _A_($UHC.$Base.$_3a,[$x,$__4]);});
$UHC.$Base.$__78__2091NEW800=
 new _F_(function($p,$x,$xs)
         {var $__=
           new _A_($p,[$x]);
          var $__5=
           _e_($__);
          var $__swJSW364__0;
          switch($__5._tag_)
           {case 0:
             $__swJSW364__0=
              $UHC.$Base.$_5b_5d;
             break;
            case 1:
             var $__6=
              new _A_($UHC.$Base.$takeWhile1,[$p,$xs]);
             $__swJSW364__0=
              $__6;
             break;}
          return $__swJSW364__0;});
$UHC.$Base.$takeWhile1=
 new _F_(function($p,$__)
         {var $__3=
           _e_($__);
          var $__swJSW365__0;
          switch($__3._tag_)
           {case 0:
             var $__6=
              new _A_($UHC.$Base.$__78__2091NEW800,[$p,$__3._1,$__3._2]);
             var $__7=
              new _A_($UHC.$Base.$_3a,[$__3._1,$__6]);
             $__swJSW365__0=
              $__7;
             break;
            case 1:
             $__swJSW365__0=
              $UHC.$Base.$undefined;
             break;}
          return $__swJSW365__0;});
$UHC.$Base.$_2d=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._3;});
$UHC.$Base.$__78__5197__0=
 new _F_(function($__,$__2,$m,$delta,$_24x__75__29__0)
         {var $__6=
           new _A_($UHC.$Base.$_2d,[$__2,$m,$delta]);
          return new _A_($UHC.$Base.$_3c_3d,[$__,$_24x__75__29__0,$__6]);});
$UHC.$Base.$boundedEnumFromThenTo=
 new _F_(function($__,$__2,$__3,$__4,$n,$n_27,$m)
         {var $delta=
           new _A_($UHC.$Base.$_2d,[$__2,$n_27,$n]);
          var $__9=
           new _A_($UHC.$Base.$__78__5158__0,[$__2,$delta]);
          var $ns=
           new _A_($UHC.$Base.$iterate,[$__9,$n]);
          var $__11=
           new _A_($UHC.$Base.$_3e_3d,[$__,$n_27,$n]);
          var $__12=
           _e_($__11);
          var $__swJSW367__0;
          switch($__12._tag_)
           {case 0:
             var $__13=
              _e_($UHC.$Base.$otherwise);
             var $__swJSW368__0;
             switch($__13._tag_)
              {case 0:
                var $__14=
                 new _A_($UHC.$Base.$packedStringToString,["FAIL 75_28_0"]);
                var $__15=
                 new _A_($UHC.$Base.$error,[$__14]);
                $__swJSW368__0=
                 $__15;
                break;
               case 1:
                var $__16=
                 new _A_($UHC.$Base.$_3e_3d,[$__,$n,$m]);
                var $__17=
                 _e_($__16);
                var $__swJSW369__0;
                switch($__17._tag_)
                 {case 0:
                   $__swJSW369__0=
                    $UHC.$Base.$_5b_5d;
                   break;
                  case 1:
                   var $__18=
                    new _A_($UHC.$Base.$__78__5181__0,[$__,$__2,$m,$delta]);
                   var $__19=
                    new _A_($UHC.$Base.$takeWhile1,[$__18,$ns]);
                   $__swJSW369__0=
                    $__19;
                   break;}
                $__swJSW368__0=
                 $__swJSW369__0;
                break;}
             $__swJSW367__0=
              $__swJSW368__0;
             break;
            case 1:
             var $__20=
              new _A_($UHC.$Base.$_3c_3d,[$__,$n,$m]);
             var $__21=
              _e_($__20);
             var $__swJSW370__0;
             switch($__21._tag_)
              {case 0:
                $__swJSW370__0=
                 $UHC.$Base.$_5b_5d;
                break;
               case 1:
                var $__22=
                 new _A_($UHC.$Base.$__78__5197__0,[$__,$__2,$m,$delta]);
                var $__23=
                 new _A_($UHC.$Base.$takeWhile1,[$__22,$ns]);
                $__swJSW370__0=
                 $__23;
                break;}
             $__swJSW367__0=
              $__swJSW370__0;
             break;}
          return $__swJSW367__0;});
$UHC.$Base.$signum=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._9;});
$UHC.$Base.$pNEW432UNQ1977CCN=
 new _F_(function($x1,$x2)
         {var $x23=
           _e_($x2);
          var $__swJSW372__0;
          switch($x23._tag_)
           {case 0:
             var $__=
              new _A_($x1,[$x23._1]);
             var $__7=
              _e_($__);
             var $__swJSW373__0;
             switch($__7._tag_)
              {case 0:
                var $__8=
                 _e_($UHC.$Base.$otherwise);
                var $__swJSW374__0;
                switch($__8._tag_)
                 {case 0:
                   $__swJSW374__0=
                    $UHC.$Base.$undefined;
                   break;
                  case 1:
                   $__swJSW374__0=
                    $UHC.$Base.$_5b_5d;
                   break;}
                $__swJSW373__0=
                 $__swJSW374__0;
                break;
               case 1:
                var $__9=
                 new _A_($UHC.$Base.$takeWhile,[$x1,$x23._2]);
                var $__10=
                 new _A_($UHC.$Base.$_3a,[$x23._1,$__9]);
                $__swJSW373__0=
                 $__10;
                break;}
             $__swJSW372__0=
              $__swJSW373__0;
             break;
            case 1:
             $__swJSW372__0=
              $UHC.$Base.$undefined;
             break;}
          return $__swJSW372__0;});
$UHC.$Base.$takeWhile=
 new _F_(function($x1,$x2)
         {var $p=
           new _A_($UHC.$Base.$pNEW432UNQ1977CCN,[$x1,$x2]);
          var $x24=
           _e_($x2);
          var $__swJSW375__0;
          switch($x24._tag_)
           {case 0:
             $__swJSW375__0=
              $p;
             break;
            case 1:
             $__swJSW375__0=
              $UHC.$Base.$_5b_5d;
             break;}
          return $__swJSW375__0;});
$UHC.$Base.$primDivModInt=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__2);
          return primDivModInt($__3,$__4);});
$UHC.$Base.$fromEnum=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._5;});
$UHC.$Base.$primQuotInt=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__2);
          return primQuotInt($__3,$__4);});
$UHC.$Base.$primLeInt=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__2);
          return primLeInt($__3,$__4);});
$UHC.$Base.$primGeInt=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__2);
          return primGeInt($__3,$__4);});
$UHC.$Base.$primCmpInt=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__2);
          return primCmpInt($__3,$__4);});
$UHC.$Base.$primGtInt=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__2);
          return primGtInt($__3,$__4);});
$UHC.$Base.$primLtInt=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__2);
          return primLtInt($__3,$__4);});
$UHC.$Base.$primNeInt=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__2);
          return primNeInt($__3,$__4);});
$UHC.$Base.$primEqInt=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__2);
          return primEqInt($__3,$__4);});
$UHC.$Base.$Eq__NEW1762UNQ10107EVLDCT74__88__0RDC=
 new _F_(function($Eq__)
         {var $Eq__2=
           _e_(new _A_($UHC.$Base.$Eq__CLS74__4__0,[$Eq__]));
          var $__5=
           {_tag_:0,_1:$UHC.$Base.$primNeInt,_2:$UHC.$Base.$primEqInt};
          return $__5;});
$UHC.$Base.$Eq__NEW1760UNQ10106DCT74__88__0RDC=
 new _F_(function($Eq__)
         {var $Eq__2=
           new _A_($UHC.$Base.$Eq__NEW1762UNQ10107EVLDCT74__88__0RDC,[$Eq__]);
          return $Eq__2;});
$UHC.$Base.$Eq__UNQ10106DCT74__88__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Eq__NEW1760UNQ10106DCT74__88__0RDC,[$UHC.$Base.$Eq__UNQ10106DCT74__88__0RDC]);}),[]);
$UHC.$Base.$Eq__DCT74__88__0=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$Eq__UNQ10106DCT74__88__0RDC;}),[]);
$UHC.$Base.$Ord__NEW2180UNQ10847EVLDCT74__91__0RDC=
 new _F_(function($Ord__)
         {var $Ord__2=
           _e_(new _A_($UHC.$Base.$Ord__CLS74__5__0,[$Ord__]));
          var $__11=
           {_tag_:0,_1:$UHC.$Base.$primLtInt,_2:$UHC.$Base.$primLeInt,_3:$UHC.$Base.$primGtInt,_4:$UHC.$Base.$primGeInt,_5:$UHC.$Base.$Eq__DCT74__88__0,_6:$UHC.$Base.$primCmpInt,_7:$Ord__2._7,_8:$Ord__2._8};
          return $__11;});
$UHC.$Base.$Ord__NEW2178UNQ10846DCT74__91__0RDC=
 new _F_(function($Ord__)
         {var $Ord__2=
           new _A_($UHC.$Base.$Ord__NEW2180UNQ10847EVLDCT74__91__0RDC,[$Ord__]);
          return $Ord__2;});
$UHC.$Base.$Ord__UNQ10846DCT74__91__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Ord__NEW2178UNQ10846DCT74__91__0RDC,[$UHC.$Base.$Ord__UNQ10846DCT74__91__0RDC]);}),[]);
$UHC.$Base.$Ord__DCT74__91__0=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$Ord__UNQ10846DCT74__91__0RDC;}),[]);
$UHC.$Base.$primCmpInteger=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__2);
          return primCmpInteger($__3,$__4);});
$UHC.$Base.$primEqInteger=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__2);
          return primEqInteger($__3,$__4);});
$UHC.$Base.$Eq__NEW1748UNQ10097EVLDCT74__130__0RDC=
 new _F_(function($Eq__)
         {var $Eq__2=
           _e_(new _A_($UHC.$Base.$Eq__CLS74__4__0,[$Eq__]));
          var $__5=
           {_tag_:0,_1:$Eq__2._1,_2:$UHC.$Base.$primEqInteger};
          return $__5;});
$UHC.$Base.$Eq__NEW1746UNQ10096DCT74__130__0RDC=
 new _F_(function($Eq__)
         {var $Eq__2=
           new _A_($UHC.$Base.$Eq__NEW1748UNQ10097EVLDCT74__130__0RDC,[$Eq__]);
          return $Eq__2;});
$UHC.$Base.$Eq__UNQ10096DCT74__130__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Eq__NEW1746UNQ10096DCT74__130__0RDC,[$UHC.$Base.$Eq__UNQ10096DCT74__130__0RDC]);}),[]);
$UHC.$Base.$Eq__DCT74__130__0=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$Eq__UNQ10096DCT74__130__0RDC;}),[]);
$UHC.$Base.$Ord__NEW2138UNQ10760EVLDCT74__132__0RDC=
 new _F_(function($Ord__)
         {var $Ord__2=
           _e_(new _A_($UHC.$Base.$Ord__CLS74__5__0,[$Ord__]));
          var $__11=
           {_tag_:0,_1:$Ord__2._1,_2:$Ord__2._2,_3:$Ord__2._3,_4:$Ord__2._4,_5:$UHC.$Base.$Eq__DCT74__130__0,_6:$UHC.$Base.$primCmpInteger,_7:$Ord__2._7,_8:$Ord__2._8};
          return $__11;});
$UHC.$Base.$Ord__NEW2136UNQ10759DCT74__132__0RDC=
 new _F_(function($Ord__)
         {var $Ord__2=
           new _A_($UHC.$Base.$Ord__NEW2138UNQ10760EVLDCT74__132__0RDC,[$Ord__]);
          return $Ord__2;});
$UHC.$Base.$Ord__UNQ10759DCT74__132__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Ord__NEW2136UNQ10759DCT74__132__0RDC,[$UHC.$Base.$Ord__UNQ10759DCT74__132__0RDC]);}),[]);
$UHC.$Base.$Ord__DCT74__132__0=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$Ord__UNQ10759DCT74__132__0RDC;}),[]);
$UHC.$Base.$enumFromThenTo=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._3;});
$UHC.$Base.$primRemInteger=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__2);
          return $__3.remainder($__4);});
$UHC.$Base.$toEnum=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._8;});
$UHC.$Base.$Num__DCT74__134__0DFLUHC_2eBase_2efromInteger=
 new _F_(function($x)
         {return $x;});
$UHC.$Base.$Num__NEW4659UNQ10649DCT74__134__0RDC=
 new _F_(function($Num__,$Num__2,$Num__3)
         {var $Num__4=
           new _A_($UHC.$Base.$Num__NEW4663UNQ10654EVLDCT74__134__0RDC,[$Num__,$Num__2,$Num__3]);
          return $Num__4;});
$UHC.$Base.$Num__NEW4663UNQ10654EVLDCT74__134__0RDC=
 new _F_(function($Num__,$Num__2,$Num__3)
         {var $Num__4=
           _e_(new _A_($UHC.$Base.$Num__CLS74__11__0,[$Num__2]));
          var $__14=
           {_tag_:0,_1:$UHC.$Base.$primMulInteger,_2:$UHC.$Base.$primAddInteger,_3:$UHC.$Base.$primSubInteger,_4:$UHC.$Base.$Eq__DCT74__130__0,_5:$Num__,_6:$UHC.$Base.$primIntToInteger,_7:$UHC.$Base.$Num__DCT74__134__0DFLUHC_2eBase_2efromInteger,_8:$UHC.$Base.$primNegInteger,_9:$Num__3};
          return $__14;});
$UHC.$Base.$Num__DCT74__134__0DFLUHC_2eBase_2eabs=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$absReal,[$UHC.$Base.$Ord__DCT74__132__0,$UHC.$Base.$Num__UNQ10649DCT74__134__0RDC]);}),[]);
$UHC.$Base.$Num__UNQ10649DCT74__134__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Num__NEW4659UNQ10649DCT74__134__0RDC,[$UHC.$Base.$Num__DCT74__134__0DFLUHC_2eBase_2eabs,$UHC.$Base.$Num__UNQ10649DCT74__134__0RDC,$UHC.$Base.$Num__DCT74__134__0DFLUHC_2eBase_2esignum]);}),[]);
$UHC.$Base.$Num__DCT74__134__0DFLUHC_2eBase_2esignum=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$signumReal,[$UHC.$Base.$Ord__DCT74__132__0,$UHC.$Base.$Num__UNQ10649DCT74__134__0RDC]);}),[]);
$UHC.$Base.$Num__CLS74__11__0DFLUHC_2eBase_2e_2d=
 new _F_(function($Num__,$x,$y)
         {var $__=
           new _A_($UHC.$Base.$negate,[$Num__,$y]);
          return new _A_($UHC.$Base.$_2b,[$Num__,$x,$__]);});
$UHC.$Base.$Integral__DCT74__110__0DFLUHC_2eBase_2etoInt=
 new _F_(function($x)
         {return $x;});
$UHC.$Base.$Integral__NEW4566UNQ10882DCT74__110__0RDC=
 new _F_(function($Integral__)
         {var $Integral__2=
           new _A_($UHC.$Base.$Integral__NEW4568UNQ10883EVLDCT74__110__0RDC,[$Integral__]);
          return $Integral__2;});
$UHC.$Base.$Integral__NEW4568UNQ10883EVLDCT74__110__0RDC=
 new _F_(function($Integral__)
         {var $Integral__2=
           _e_(new _A_($UHC.$Base.$Integral__CLS74__14__0,[$Integral__]));
          var $__13=
           {_tag_:0,_1:$UHC.$Base.$Enum__DCT74__118__0,_2:$UHC.$Base.$Real__DCT74__100__0,_3:$UHC.$Base.$primDivInt,_4:$UHC.$Base.$primDivModInt,_5:$UHC.$Base.$primModInt,_6:$UHC.$Base.$primQuotInt,_7:$UHC.$Base.$primQuotRemInt,_8:$UHC.$Base.$primRemInt,_9:$UHC.$Base.$Integral__DCT74__110__0DFLUHC_2eBase_2etoInt,_10:$UHC.$Base.$primIntToInteger};
          return $__13;});
$UHC.$Base.$Integral__UNQ10882DCT74__110__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Integral__NEW4566UNQ10882DCT74__110__0RDC,[$UHC.$Base.$Integral__UNQ10882DCT74__110__0RDC]);}),[]);
$UHC.$Base.$__76__17806__2__2NEW4573UNQ4659=
 new _F_(function($Integral__)
         {var $Real__=
           _e_($Integral__);
          return $Real__._2;});
$UHC.$Base.$Integral__CLS74__14__0DFLUHC_2eBase_2erem=
 new _F_(function($Integral__,$n,$d)
         {var $__=
           new _A_($UHC.$Base.$quotRem,[$Integral__,$n,$d]);
          var $q=
           new _A_($UHC.$Base.$qNEW4578UNQ4751,[$__]);
          var $r=
           new _A_($UHC.$Base.$rNEW4581UNQ4752,[$__]);
          return $r;});
$UHC.$Base.$qNEW4578UNQ4751=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return $__2[0];});
$UHC.$Base.$rNEW4581UNQ4752=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return $__2[1];});
$UHC.$Base.$Integral__CLS74__14__0DFLUHC_2eBase_2ediv=
 new _F_(function($Integral__,$n,$d)
         {var $__=
           new _A_($UHC.$Base.$divMod,[$Integral__,$n,$d]);
          var $q=
           new _A_($UHC.$Base.$qNEW4586UNQ4686,[$__]);
          var $r=
           new _A_($UHC.$Base.$rNEW4589UNQ4687,[$__]);
          return $q;});
$UHC.$Base.$qNEW4586UNQ4686=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return $__2[0];});
$UHC.$Base.$rNEW4589UNQ4687=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return $__2[1];});
$UHC.$Base.$Integral__CLS74__14__0DFLUHC_2eBase_2emod=
 new _F_(function($Integral__,$n,$d)
         {var $__=
           new _A_($UHC.$Base.$divMod,[$Integral__,$n,$d]);
          var $r=
           new _A_($UHC.$Base.$rNEW4597UNQ4722,[$__]);
          var $q=
           new _A_($UHC.$Base.$qNEW4600UNQ4721,[$__]);
          return $r;});
$UHC.$Base.$rNEW4597UNQ4722=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return $__2[1];});
$UHC.$Base.$qNEW4600UNQ4721=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return $__2[0];});
$UHC.$Base.$__76__18135__2__0NEW4603UNQ4661=
 new _F_(function($__)
         {var $Num__=
           _e_($__);
          return $Num__._1;});
$UHC.$Base.$__76__18058__2__0NEW4606UNQ4666=
 new _F_(function($__)
         {var $Eq__=
           _e_($__);
          return $Eq__._4;});
$UHC.$Base.$Integral__CLS74__14__0DFLUHC_2eBase_2edivMod=
 new _F_(function($__,$__2,$Integral__,$n,$d)
         {var $qr=
           new _A_($UHC.$Base.$quotRem,[$Integral__,$n,$d]);
          var $r=
           new _A_($UHC.$Base.$rNEW4611UNQ4705,[$qr]);
          var $q=
           new _A_($UHC.$Base.$qNEW4614UNQ4704,[$qr]);
          var $__9=
           new _A_($UHC.$Base.$signum,[$__,$d]);
          var $__10=
           new _A_($UHC.$Base.$negate,[$__,$__9]);
          var $__11=
           new _A_($UHC.$Base.$signum,[$__,$r]);
          var $__12=
           new _A_($UHC.$Base.$_3d_3d,[$__2,$__11,$__10]);
          var $__13=
           _e_($__12);
          var $__swJSW394__0;
          switch($__13._tag_)
           {case 0:
             $__swJSW394__0=
              $qr;
             break;
            case 1:
             var $__14=
              new _A_($UHC.$Base.$_2b,[$__,$r,$d]);
             var $__15=
              new _A_($UHC.$Base.$packedStringToInteger,["1"]);
             var $__16=
              new _A_($UHC.$Base.$fromInteger,[$__,$__15]);
             var $__17=
              new _A_($UHC.$Base.$_2d,[$__,$q,$__16]);
             var $__18=
              [$__17,$__14];
             $__swJSW394__0=
              $__18;
             break;}
          return $__swJSW394__0;});
$UHC.$Base.$rNEW4611UNQ4705=
 new _F_(function($qr)
         {var $qr2=
           _e_($qr);
          return $qr2[1];});
$UHC.$Base.$qNEW4614UNQ4704=
 new _F_(function($qr)
         {var $qr2=
           _e_($qr);
          return $qr2[0];});
$UHC.$Base.$Integral__CLS74__14__0DFLUHC_2eBase_2equot=
 new _F_(function($Integral__,$n,$d)
         {var $__=
           new _A_($UHC.$Base.$quotRem,[$Integral__,$n,$d]);
          var $q=
           new _A_($UHC.$Base.$qNEW4629UNQ4736,[$__]);
          var $r=
           new _A_($UHC.$Base.$rNEW4632UNQ4737,[$__]);
          return $q;});
$UHC.$Base.$qNEW4629UNQ4736=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return $__2[0];});
$UHC.$Base.$rNEW4632UNQ4737=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return $__2[1];});
$UHC.$Base.$Integral__DCT74__143__0DFLUHC_2eBase_2etoInteger=
 new _F_(function($x)
         {return $x;});
$UHC.$Base.$Integral__NEW4638UNQ10868DCT74__143__0RDC=
 new _F_(function($Integral__)
         {var $Integral__2=
           new _A_($UHC.$Base.$Integral__NEW4640UNQ10869EVLDCT74__143__0RDC,[$Integral__]);
          return $Integral__2;});
$UHC.$Base.$Integral__NEW4640UNQ10869EVLDCT74__143__0RDC=
 new _F_(function($Integral__)
         {var $Integral__2=
           _e_(new _A_($UHC.$Base.$Integral__CLS74__14__0,[$Integral__]));
          var $__13=
           {_tag_:0,_1:$UHC.$Base.$Enum__DCT74__151__0,_2:$UHC.$Base.$Real__DCT74__142__0,_3:$UHC.$Base.$primDivInteger,_4:$UHC.$Base.$primDivModInteger,_5:$UHC.$Base.$primModInteger,_6:$UHC.$Base.$primQuotInteger,_7:$UHC.$Base.$primQuotRemInteger,_8:$UHC.$Base.$primRemInteger,_9:$UHC.$Base.$primIntegerToInt,_10:$UHC.$Base.$Integral__DCT74__143__0DFLUHC_2eBase_2etoInteger};
          return $__13;});
$UHC.$Base.$Integral__UNQ10868DCT74__143__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Integral__NEW4638UNQ10868DCT74__143__0RDC,[$UHC.$Base.$Integral__UNQ10868DCT74__143__0RDC]);}),[]);
$UHC.$Base.$Enum__DCT74__151__0DFLUHC_2eBase_2eenumFromThenTo=
 new _F_(function($n,$n2,$m)
         {var $p=
           new _A_($UHC.$Base.$pNEW4672UNQ11353,[$n,$n2,$m]);
          var $__=
           new _A_($UHC.$Base.$numericEnumFromThen,[$UHC.$Base.$Num__DCT74__134__0,$n,$n2]);
          return new _A_($UHC.$Base.$takeWhile,[$p,$__]);});
$UHC.$Base.$pNEW4672UNQ11353=
 new _F_(function($n,$n2,$m)
         {var $__=
           new _A_($UHC.$Base.$_3e_3d,[$UHC.$Base.$Ord__DCT74__132__0,$n2,$n]);
          var $__5=
           _e_($__);
          var $__swJSW400__0;
          switch($__5._tag_)
           {case 0:
             var $__6=
              _e_($UHC.$Base.$otherwise);
             var $__swJSW401__0;
             switch($__6._tag_)
              {case 0:
                var $__7=
                 new _A_($UHC.$Base.$packedStringToString,["FAIL 75_308_0"]);
                var $__8=
                 new _A_($UHC.$Base.$error,[$__7]);
                $__swJSW401__0=
                 $__8;
                break;
               case 1:
                $__swJSW401__0=
                 new _A_($UHC.$Base.$__78__9200__0,[$m]);
                break;}
             $__swJSW400__0=
              $__swJSW401__0;
             break;
            case 1:
             $__swJSW400__0=
              new _A_($UHC.$Base.$__78__9205__0,[$m]);
             break;}
          return $__swJSW400__0;});
$UHC.$Base.$__78__9200__0=
 new _F_(function($m,$_24x__75__310__0)
         {return new _A_($UHC.$Base.$_3e_3d,[$UHC.$Base.$Ord__DCT74__132__0,$_24x__75__310__0,$m]);});
$UHC.$Base.$__78__9205__0=
 new _F_(function($m,$_24x__75__309__0)
         {return new _A_($UHC.$Base.$_3c_3d,[$UHC.$Base.$Ord__DCT74__132__0,$_24x__75__309__0,$m]);});
$UHC.$Base.$Enum__DCT74__151__0DFLUHC_2eBase_2esucc=
 new _F_(function($x)
         {var $__=
           new _A_($UHC.$Base.$primIntToInteger,[1]);
          return new _A_($UHC.$Base.$_2b,[$UHC.$Base.$Num__DCT74__134__0,$x,$__]);});
$UHC.$Base.$Enum__DCT74__151__0DFLUHC_2eBase_2eenumFromThen=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$numericEnumFromThen,[$UHC.$Base.$Num__DCT74__134__0]);}),[]);
$UHC.$Base.$Enum__DCT74__151__0DFLUHC_2eBase_2epred=
 new _F_(function($x)
         {var $__=
           new _A_($UHC.$Base.$primIntToInteger,[1]);
          return new _A_($UHC.$Base.$_2d,[$UHC.$Base.$Num__DCT74__134__0,$x,$__]);});
$UHC.$Base.$Enum__DCT74__151__0DFLUHC_2eBase_2eenumFrom=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$numericEnumFrom,[$UHC.$Base.$Num__DCT74__134__0]);}),[]);
$UHC.$Base.$Enum__DCT74__151__0DFLUHC_2eBase_2eenumFromTo=
 new _F_(function($n,$m)
         {var $__=
           new _A_($UHC.$Base.$numericEnumFrom,[$UHC.$Base.$Num__DCT74__134__0,$n]);
          var $__4=
           new _A_($UHC.$Base.$__78__9240__0,[$m]);
          return new _A_($UHC.$Base.$takeWhile,[$__4,$__]);});
$UHC.$Base.$__78__9240__0=
 new _F_(function($m,$_24x__75__306__0)
         {return new _A_($UHC.$Base.$_3c_3d,[$UHC.$Base.$Ord__DCT74__132__0,$_24x__75__306__0,$m]);});
$UHC.$Base.$Enum__NEW4693UNQ11318DCT74__151__0RDC=
 new _F_(function($Enum__,$Enum__2,$Enum__3)
         {var $Enum__4=
           new _A_($UHC.$Base.$Enum__NEW4697UNQ11328EVLDCT74__151__0RDC,[$Enum__,$Enum__2,$Enum__3]);
          return $Enum__4;});
$UHC.$Base.$Enum__NEW4697UNQ11328EVLDCT74__151__0RDC=
 new _F_(function($Enum__,$Enum__2,$Enum__3)
         {var $Enum__4=
           _e_(new _A_($UHC.$Base.$Enum__CLS74__38__0,[$Enum__]));
          var $__13=
           {_tag_:0,_1:$Enum__2,_2:$Enum__3,_3:$UHC.$Base.$Enum__DCT74__151__0DFLUHC_2eBase_2eenumFromThenTo,_4:$UHC.$Base.$Enum__DCT74__151__0DFLUHC_2eBase_2eenumFromTo,_5:$UHC.$Base.$primIntegerToInt,_6:$UHC.$Base.$Enum__DCT74__151__0DFLUHC_2eBase_2epred,_7:$UHC.$Base.$Enum__DCT74__151__0DFLUHC_2eBase_2esucc,_8:$UHC.$Base.$primIntToInteger};
          return $__13;});
$UHC.$Base.$Enum__UNQ11318DCT74__151__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Enum__NEW4693UNQ11318DCT74__151__0RDC,[$UHC.$Base.$Enum__UNQ11318DCT74__151__0RDC,$UHC.$Base.$Enum__DCT74__151__0DFLUHC_2eBase_2eenumFrom,$UHC.$Base.$Enum__DCT74__151__0DFLUHC_2eBase_2eenumFromThen]);}),[]);
$UHC.$Base.$Enum__CLS74__38__0DFLUHC_2eBase_2eenumFrom=
 new _F_(function($Enum__,$x)
         {var $__=
           new _A_($UHC.$Base.$fromEnum,[$Enum__,$x]);
          var $__4=
           new _A_($UHC.$Base.$enumFrom,[$UHC.$Base.$Enum__DCT74__118__0,$__]);
          var $__5=
           new _A_($UHC.$Base.$toEnum,[$Enum__]);
          return new _A_($UHC.$Base.$map,[$__5,$__4]);});
$UHC.$Base.$Enum__CLS74__38__0DFLUHC_2eBase_2eenumFromThen=
 new _F_(function($Enum__,$x,$y)
         {var $__=
           new _A_($UHC.$Base.$fromEnum,[$Enum__,$y]);
          var $__5=
           new _A_($UHC.$Base.$fromEnum,[$Enum__,$x]);
          var $__6=
           new _A_($UHC.$Base.$enumFromThen,[$UHC.$Base.$Enum__DCT74__118__0,$__5,$__]);
          var $__7=
           new _A_($UHC.$Base.$toEnum,[$Enum__]);
          return new _A_($UHC.$Base.$map,[$__7,$__6]);});
$UHC.$Base.$Enum__CLS74__38__0DFLUHC_2eBase_2eenumFromThenTo=
 new _F_(function($Enum__,$x,$y,$z)
         {var $__=
           new _A_($UHC.$Base.$fromEnum,[$Enum__,$z]);
          var $__6=
           new _A_($UHC.$Base.$fromEnum,[$Enum__,$y]);
          var $__7=
           new _A_($UHC.$Base.$fromEnum,[$Enum__,$x]);
          var $__8=
           new _A_($UHC.$Base.$enumFromThenTo,[$UHC.$Base.$Enum__DCT74__118__0,$__7,$__6,$__]);
          var $__9=
           new _A_($UHC.$Base.$toEnum,[$Enum__]);
          return new _A_($UHC.$Base.$map,[$__9,$__8]);});
$UHC.$Base.$Enum__CLS74__38__0DFLUHC_2eBase_2eenumFromTo=
 new _F_(function($Enum__,$x,$y)
         {var $__=
           new _A_($UHC.$Base.$fromEnum,[$Enum__,$y]);
          var $__5=
           new _A_($UHC.$Base.$fromEnum,[$Enum__,$x]);
          var $__6=
           new _A_($UHC.$Base.$enumFromTo,[$UHC.$Base.$Enum__DCT74__118__0,$__5,$__]);
          var $__7=
           new _A_($UHC.$Base.$toEnum,[$Enum__]);
          return new _A_($UHC.$Base.$map,[$__7,$__6]);});
$UHC.$Base.$Enum__NEW4520UNQ10418DCT74__118__0RDC=
 new _F_(function($Enum__,$Enum__2,$Enum__3,$Enum__4,$Enum__5,$Enum__6,$Enum__7)
         {var $Enum__8=
           new _A_($UHC.$Base.$Enum__NEW4528UNQ10438EVLDCT74__118__0RDC,[$Enum__,$Enum__2,$Enum__3,$Enum__4,$Enum__5,$Enum__6,$Enum__7]);
          return $Enum__8;});
$UHC.$Base.$Enum__NEW4528UNQ10438EVLDCT74__118__0RDC=
 new _F_(function($Enum__,$Enum__2,$Enum__3,$Enum__4,$Enum__5,$Enum__6,$Enum__7)
         {var $Enum__8=
           _e_(new _A_($UHC.$Base.$Enum__CLS74__38__0,[$Enum__5]));
          var $__17=
           {_tag_:0,_1:$Enum__7,_2:$Enum__,_3:$Enum__3,_4:$Enum__6,_5:$UHC.$Base.$id,_6:$Enum__2,_7:$Enum__4,_8:$UHC.$Base.$id};
          return $__17;});
$UHC.$Base.$Enum__DCT74__118__0DFLUHC_2eBase_2eenumFromThen=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$boundedEnumFromThen,[$UHC.$Base.$Ord__DCT74__91__0,$UHC.$Base.$Bounded__DCT74__97__0,$UHC.$Base.$Enum__UNQ10418DCT74__118__0RDC]);}),[]);
$UHC.$Base.$Enum__UNQ10418DCT74__118__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Enum__NEW4520UNQ10418DCT74__118__0RDC,[$UHC.$Base.$Enum__DCT74__118__0DFLUHC_2eBase_2eenumFromThen,$UHC.$Base.$Enum__DCT74__118__0DFLUHC_2eBase_2epred,$UHC.$Base.$Enum__DCT74__118__0DFLUHC_2eBase_2eenumFromThenTo,$UHC.$Base.$Enum__DCT74__118__0DFLUHC_2eBase_2esucc,$UHC.$Base.$Enum__UNQ10418DCT74__118__0RDC,$UHC.$Base.$Enum__DCT74__118__0DFLUHC_2eBase_2eenumFromTo,$UHC.$Base.$Enum__DCT74__118__0DFLUHC_2eBase_2eenumFrom]);}),[]);
$UHC.$Base.$Enum__DCT74__118__0DFLUHC_2eBase_2epred=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$boundedPred,[$UHC.$Base.$Num__DCT74__101__0,$UHC.$Base.$Bounded__DCT74__97__0,$UHC.$Base.$Enum__UNQ10418DCT74__118__0RDC]);}),[]);
$UHC.$Base.$Enum__DCT74__118__0DFLUHC_2eBase_2eenumFromThenTo=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$boundedEnumFromThenTo,[$UHC.$Base.$Ord__DCT74__91__0,$UHC.$Base.$Num__DCT74__101__0,$UHC.$Base.$Bounded__DCT74__97__0,$UHC.$Base.$Enum__UNQ10418DCT74__118__0RDC]);}),[]);
$UHC.$Base.$Enum__DCT74__118__0DFLUHC_2eBase_2esucc=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$boundedSucc,[$UHC.$Base.$Num__DCT74__101__0,$UHC.$Base.$Bounded__DCT74__97__0,$UHC.$Base.$Enum__UNQ10418DCT74__118__0RDC]);}),[]);
$UHC.$Base.$Enum__DCT74__118__0DFLUHC_2eBase_2eenumFromTo=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$boundedEnumFromTo,[$UHC.$Base.$Ord__DCT74__91__0,$UHC.$Base.$Bounded__DCT74__97__0,$UHC.$Base.$Enum__UNQ10418DCT74__118__0RDC]);}),[]);
$UHC.$Base.$Enum__DCT74__118__0DFLUHC_2eBase_2eenumFrom=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$boundedEnumFrom,[$UHC.$Base.$Ord__DCT74__91__0,$UHC.$Base.$Bounded__DCT74__97__0,$UHC.$Base.$Enum__UNQ10418DCT74__118__0RDC]);}),[]);
$UHC.$Base.$Num__NEW4544UNQ10666DCT74__101__0RDC=
 new _F_(function($Num__,$Num__2,$Num__3)
         {var $Num__4=
           new _A_($UHC.$Base.$Num__NEW4548UNQ10671EVLDCT74__101__0RDC,[$Num__,$Num__2,$Num__3]);
          return $Num__4;});
$UHC.$Base.$Num__NEW4548UNQ10671EVLDCT74__101__0RDC=
 new _F_(function($Num__,$Num__2,$Num__3)
         {var $Num__4=
           _e_(new _A_($UHC.$Base.$Num__CLS74__11__0,[$Num__]));
          var $__14=
           {_tag_:0,_1:$UHC.$Base.$primMulInt,_2:$UHC.$Base.$primAddInt,_3:$UHC.$Base.$primSubInt,_4:$UHC.$Base.$Eq__DCT74__88__0,_5:$Num__3,_6:$UHC.$Base.$id,_7:$UHC.$Base.$primIntegerToInt,_8:$UHC.$Base.$primNegInt,_9:$Num__2};
          return $__14;});
$UHC.$Base.$Num__UNQ10666DCT74__101__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Num__NEW4544UNQ10666DCT74__101__0RDC,[$UHC.$Base.$Num__UNQ10666DCT74__101__0RDC,$UHC.$Base.$Num__DCT74__101__0DFLUHC_2eBase_2esignum,$UHC.$Base.$Num__DCT74__101__0DFLUHC_2eBase_2eabs]);}),[]);
$UHC.$Base.$Num__DCT74__101__0DFLUHC_2eBase_2esignum=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$signumReal,[$UHC.$Base.$Ord__DCT74__91__0,$UHC.$Base.$Num__UNQ10666DCT74__101__0RDC]);}),[]);
$UHC.$Base.$Num__DCT74__101__0DFLUHC_2eBase_2eabs=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$absReal,[$UHC.$Base.$Ord__DCT74__91__0,$UHC.$Base.$Num__UNQ10666DCT74__101__0RDC]);}),[]);
$UHC.$Base.$Real__DCT74__142__0DFLUHC_2eBase_2etoRational=
 new _F_(function($x)
         {var $__=
           new _A_($UHC.$Base.$primIntToInteger,[1]);
          return new _A_($UHC.$Base.$_25,[$UHC.$Base.$Integral__DCT74__143__0,$x,$__]);});
$UHC.$Base.$Real__NEW4647UNQ10911DCT74__142__0RDC=
 new _F_(function($Real__)
         {var $Real__2=
           new _A_($UHC.$Base.$Real__NEW4649UNQ10914EVLDCT74__142__0RDC,[$Real__]);
          return $Real__2;});
$UHC.$Base.$Real__NEW4649UNQ10914EVLDCT74__142__0RDC=
 new _F_(function($Real__)
         {var $Real__2=
           _e_(new _A_($UHC.$Base.$Real__CLS74__13__0,[$Real__]));
          var $__6=
           {_tag_:0,_1:$UHC.$Base.$Num__DCT74__134__0,_2:$UHC.$Base.$Ord__DCT74__132__0,_3:$UHC.$Base.$Real__DCT74__142__0DFLUHC_2eBase_2etoRational};
          return $__6;});
$UHC.$Base.$Real__UNQ10911DCT74__142__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Real__NEW4647UNQ10911DCT74__142__0RDC,[$UHC.$Base.$Real__UNQ10911DCT74__142__0RDC]);}),[]);
$UHC.$Base.$__76__46633__2__0NEW4653UNQ10912=
 new _F_(function($Real__)
         {var $Num__=
           _e_($Real__);
          return $Num__._1;});
$UHC.$Base.$__76__46633__2__0UNQ10912=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$__76__46633__2__0NEW4653UNQ10912,[$UHC.$Base.$Real__UNQ10911DCT74__142__0RDC]);}),[]);
$UHC.$Base.$Real__DCT74__100__0DFLUHC_2eBase_2etoRational=
 new _F_(function($x)
         {var $__=
           new _A_($UHC.$Base.$primIntToInteger,[1]);
          var $__3=
           new _A_($UHC.$Base.$toInteger,[$UHC.$Base.$Integral__DCT74__110__0,$x]);
          return new _A_($UHC.$Base.$_25,[$UHC.$Base.$Integral__DCT74__143__0,$__3,$__]);});
$UHC.$Base.$Real__NEW4707UNQ10936DCT74__100__0RDC=
 new _F_(function($Real__)
         {var $Real__2=
           new _A_($UHC.$Base.$Real__NEW4709UNQ10940EVLDCT74__100__0RDC,[$Real__]);
          return $Real__2;});
$UHC.$Base.$Real__NEW4709UNQ10940EVLDCT74__100__0RDC=
 new _F_(function($Real__)
         {var $Real__2=
           _e_(new _A_($UHC.$Base.$Real__CLS74__13__0,[$Real__]));
          var $__6=
           {_tag_:0,_1:$UHC.$Base.$Num__DCT74__101__0,_2:$UHC.$Base.$Ord__DCT74__91__0,_3:$UHC.$Base.$Real__DCT74__100__0DFLUHC_2eBase_2etoRational};
          return $__6;});
$UHC.$Base.$Real__UNQ10936DCT74__100__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Real__NEW4707UNQ10936DCT74__100__0RDC,[$UHC.$Base.$Real__UNQ10936DCT74__100__0RDC]);}),[]);
$UHC.$Base.$Num__DCT74__134__0=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$Num__UNQ10649DCT74__134__0RDC;}),[]);
$UHC.$Base.$Integral__DCT74__110__0=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$Integral__UNQ10882DCT74__110__0RDC;}),[]);
$UHC.$Base.$Integral__DCT74__143__0=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$Integral__UNQ10868DCT74__143__0RDC;}),[]);
$UHC.$Base.$Enum__DCT74__151__0=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$Enum__UNQ11318DCT74__151__0RDC;}),[]);
$UHC.$Base.$Enum__DCT74__118__0=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$Enum__UNQ10418DCT74__118__0RDC;}),[]);
$UHC.$Base.$Num__DCT74__101__0=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$Num__UNQ10666DCT74__101__0RDC;}),[]);
$UHC.$Base.$Real__DCT74__142__0=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$Real__UNQ10911DCT74__142__0RDC;}),[]);
$UHC.$Base.$Real__DCT74__100__0=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$Real__UNQ10936DCT74__100__0RDC;}),[]);
$UHC.$Base.$Num__CLS74__11__0=
 new _F_(function($Num__)
         {var $__=
           new _A_($UHC.$Base.$packedStringToInteger,["0"]);
          var $__3=
           new _A_($UHC.$Base.$fromInteger,[$Num__,$__]);
          var $Num__CLS74__11__0DFLUHC_2eBase_2enegate=
           new _A_($UHC.$Base.$_2d,[$Num__,$__3]);
          var $Num__CLS74__11__0DFLUHC_2eBase_2efromInt=
           new _A_($UHC.$Base.$fromIntegral,[$UHC.$Base.$Integral__DCT74__110__0,$Num__]);
          var $__4=
           new _A_($UHC.$Base.$Num__CLS74__11__0DFLUHC_2eBase_2e_2d,[$Num__]);
          var $Num__5=
           {_tag_:0,_1:$UHC.$Base.$undefined,_2:$UHC.$Base.$undefined,_3:$__4,_4:$UHC.$Base.$undefined,_5:$UHC.$Base.$undefined,_6:$Num__CLS74__11__0DFLUHC_2eBase_2efromInt,_7:$UHC.$Base.$undefined,_8:$Num__CLS74__11__0DFLUHC_2eBase_2enegate,_9:$UHC.$Base.$undefined};
          return $Num__5;});
$UHC.$Base.$Integral__CLS74__14__0=
 new _F_(function($Integral__)
         {var $__=
           new _A_($UHC.$Base.$__76__17806__2__2NEW4573UNQ4659,[$Integral__]);
          var $__3=
           new _A_($UHC.$Base.$toInteger,[$Integral__]);
          var $__4=
           new _A_($UHC.$Base.$toInt,[$UHC.$Base.$Integral__DCT74__143__0]);
          var $Integral__CLS74__14__0DFLUHC_2eBase_2etoInt=
           new _A_($UHC.$Base.$_2e,[$__4,$__3]);
          var $__5=
           new _A_($UHC.$Base.$__76__18135__2__0NEW4603UNQ4661,[$__]);
          var $__6=
           new _A_($UHC.$Base.$__76__18058__2__0NEW4606UNQ4666,[$__5]);
          var $__7=
           new _A_($UHC.$Base.$Integral__CLS74__14__0DFLUHC_2eBase_2erem,[$Integral__]);
          var $__8=
           new _A_($UHC.$Base.$Integral__CLS74__14__0DFLUHC_2eBase_2equot,[$Integral__]);
          var $__9=
           new _A_($UHC.$Base.$Integral__CLS74__14__0DFLUHC_2eBase_2emod,[$Integral__]);
          var $__10=
           new _A_($UHC.$Base.$Integral__CLS74__14__0DFLUHC_2eBase_2edivMod,[$__5,$__6,$Integral__]);
          var $__11=
           new _A_($UHC.$Base.$Integral__CLS74__14__0DFLUHC_2eBase_2ediv,[$Integral__]);
          var $Integral__12=
           {_tag_:0,_1:$UHC.$Base.$undefined,_2:$UHC.$Base.$undefined,_3:$__11,_4:$__10,_5:$__9,_6:$__8,_7:$UHC.$Base.$undefined,_8:$__7,_9:$Integral__CLS74__14__0DFLUHC_2eBase_2etoInt,_10:$UHC.$Base.$undefined};
          return $Integral__12;});
$UHC.$Base.$Enum__CLS74__38__0=
 new _F_(function($Enum__)
         {var $__=
           new _A_($UHC.$Base.$fromEnum,[$Enum__]);
          var $__3=
           new _A_($UHC.$Base.$_2b,[$UHC.$Base.$Num__DCT74__101__0,1]);
          var $__4=
           new _A_($UHC.$Base.$_2e,[$__3,$__]);
          var $__5=
           new _A_($UHC.$Base.$toEnum,[$Enum__]);
          var $Enum__CLS74__38__0DFLUHC_2eBase_2esucc=
           new _A_($UHC.$Base.$_2e,[$__5,$__4]);
          var $__6=
           new _A_($UHC.$Base.$fromEnum,[$Enum__]);
          var $__7=
           new _A_($UHC.$Base.$subtract,[$UHC.$Base.$Num__DCT74__101__0,1]);
          var $__8=
           new _A_($UHC.$Base.$_2e,[$__7,$__6]);
          var $__9=
           new _A_($UHC.$Base.$toEnum,[$Enum__]);
          var $Enum__CLS74__38__0DFLUHC_2eBase_2epred=
           new _A_($UHC.$Base.$_2e,[$__9,$__8]);
          var $__10=
           new _A_($UHC.$Base.$Enum__CLS74__38__0DFLUHC_2eBase_2eenumFromTo,[$Enum__]);
          var $__11=
           new _A_($UHC.$Base.$Enum__CLS74__38__0DFLUHC_2eBase_2eenumFromThenTo,[$Enum__]);
          var $__12=
           new _A_($UHC.$Base.$Enum__CLS74__38__0DFLUHC_2eBase_2eenumFromThen,[$Enum__]);
          var $__13=
           new _A_($UHC.$Base.$Enum__CLS74__38__0DFLUHC_2eBase_2eenumFrom,[$Enum__]);
          var $Enum__14=
           {_tag_:0,_1:$__13,_2:$__12,_3:$__11,_4:$__10,_5:$UHC.$Base.$undefined,_6:$Enum__CLS74__38__0DFLUHC_2eBase_2epred,_7:$Enum__CLS74__38__0DFLUHC_2eBase_2esucc,_8:$UHC.$Base.$undefined};
          return $Enum__14;});
$UHC.$Base.$primIntToChar=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return primUnsafeId($__2);});
$UHC.$Base.$primCharToInt=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return primUnsafeId($__2);});
$UHC.$Base.$Enum__NEW4716UNQ10449EVLDCT74__60__0RDC=
 new _F_(function($Enum__)
         {var $Enum__2=
           _e_(new _A_($UHC.$Base.$Enum__CLS74__38__0,[$Enum__]));
          var $__11=
           {_tag_:0,_1:$Enum__2._1,_2:$Enum__2._2,_3:$Enum__2._3,_4:$Enum__2._4,_5:$UHC.$Base.$primCharToInt,_6:$Enum__2._6,_7:$Enum__2._7,_8:$UHC.$Base.$primIntToChar};
          return $__11;});
$UHC.$Base.$Enum__NEW4714UNQ10448DCT74__60__0RDC=
 new _F_(function($Enum__)
         {var $Enum__2=
           new _A_($UHC.$Base.$Enum__NEW4716UNQ10449EVLDCT74__60__0RDC,[$Enum__]);
          return $Enum__2;});
$UHC.$Base.$Enum__UNQ10448DCT74__60__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Enum__NEW4714UNQ10448DCT74__60__0RDC,[$UHC.$Base.$Enum__UNQ10448DCT74__60__0RDC]);}),[]);
$UHC.$Base.$Enum__DCT74__60__0=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$Enum__UNQ10448DCT74__60__0RDC;}),[]);
$UHC.$Base.$__78__9294=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$enumFromTo,[$UHC.$Base.$Enum__DCT74__60__0,0,32]);}),[]);
$UHC.$Base.$asciiTab=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$zip,[$UHC.$Base.$__78__9294,$UHC.$Base.$__78__9297]);}),[]);
$UHC.$Base.$_24okUNQ7707=
 new _F_(function($mne,$_24x)
         {var $__=
           _e_($_24x);
          var $__6=
           _e_($__[0]);
          var $__swJSW410__0;
          switch($__6._tag_)
           {case 0:
             $__swJSW410__0=
              $UHC.$Base.$_5b_5d;
             break;
            case 1:
             var $__9=
              [$mne,$__[1]];
             var $__10=
              new _A_($UHC.$Base.$_3a,[$__9,$UHC.$Base.$_5b_5d]);
             $__swJSW410__0=
              $__10;
             break;}
          return $__swJSW410__0;});
$UHC.$Base.$lexmatch=
 new _F_(function($__,$x1,$x2)
         {var $__4=
           [$x1,$x2];
          var $x15=
           _e_($x1);
          var $__swJSW411__0;
          switch($x15._tag_)
           {case 0:
             var $x28=
              _e_($x2);
             var $__swJSW412__0;
             switch($x28._tag_)
              {case 0:
                var $__11=
                 new _A_($UHC.$Base.$_3d_3d,[$__,$x15._1,$x28._1]);
                var $__12=
                 _e_($__11);
                var $__swJSW413__0;
                switch($__12._tag_)
                 {case 0:
                   $__swJSW413__0=
                    $__4;
                   break;
                  case 1:
                   var $__13=
                    new _A_($UHC.$Base.$lexmatch,[$__,$x15._2,$x28._2]);
                   $__swJSW413__0=
                    $__13;
                   break;}
                $__swJSW412__0=
                 $__swJSW413__0;
                break;
               case 1:
                $__swJSW412__0=
                 $__4;
                break;}
             $__swJSW411__0=
              $__swJSW412__0;
             break;
            case 1:
             $__swJSW411__0=
              $__4;
             break;}
          return $__swJSW411__0;});
$UHC.$Base.$_24okUNQ7692=
 new _F_(function($__,$_24x)
         {var $__3=
           _e_($_24x);
          var $__6=
           new _A_($UHC.$Base.$lexmatch,[$UHC.$Base.$Eq__DCT74__56__0,$__3[1],$__]);
          var $__7=
           new _A_($UHC.$Base.$_3a,[$__6,$UHC.$Base.$_5b_5d]);
          var $__8=
           new _A_($UHC.$Base.$_24okUNQ7707,[$__3[1]]);
          return new _A_($UHC.$Base.$concatMap,[$__8,$__7]);});
$UHC.$Base.$__76__32943__0NEW4820UNQ7690=
 new _F_(function($table,$__)
         {var $__3=
           new _A_($UHC.$Base.$_24okUNQ7692,[$__]);
          return new _A_($UHC.$Base.$concatMap,[$__3,$table]);});
$UHC.$Base.$isUpper=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return primCharIsUpper($__2);});
$UHC.$Base.$__76__32620__0NEW4812UNQ7684CCN=
 new _F_(function($table,$__,$c)
         {var $__4=
           new _A_($UHC.$Base.$isDigit,[$c]);
          var $__5=
           _e_($__4);
          var $__swJSW415__0;
          switch($__5._tag_)
           {case 0:
             var $__6=
              new _A_($UHC.$Base.$isUpper,[$c]);
             var $__7=
              _e_($__6);
             var $__swJSW416__0;
             switch($__7._tag_)
              {case 0:
                $__swJSW416__0=
                 $UHC.$Base.$_5b_5d;
                break;
               case 1:
                var $__8=
                 new _A_($UHC.$Base.$__76__32943__0NEW4820UNQ7690,[$table,$__]);
                var $__9=
                 _e_($__8);
                var $__swJSW417__0;
                switch($__9._tag_)
                 {case 0:
                   var $__12=
                    new _A_($UHC.$Base.$_3a,[$__9._1,$UHC.$Base.$_5b_5d]);
                   $__swJSW417__0=
                    $__12;
                   break;
                  case 1:
                   $__swJSW417__0=
                    $UHC.$Base.$_5b_5d;
                   break;}
                $__swJSW416__0=
                 $__swJSW417__0;
                break;}
             $__swJSW415__0=
              $__swJSW416__0;
             break;
            case 1:
             var $__13=
              new _A_($UHC.$Base.$span,[$UHC.$Base.$isDigit,$__]);
             var $__14=
              new _A_($UHC.$Base.$_3a,[$__13,$UHC.$Base.$_5b_5d]);
             $__swJSW415__0=
              $__14;
             break;}
          return $__swJSW415__0;});
$UHC.$Base.$isOctDigit=
 new _F_(function($c)
         {var $__=
           new _A_($UHC.$Base.$_3c_3d,[$UHC.$Base.$Ord__DCT74__58__0,$c,55]);
          var $__3=
           new _A_($UHC.$Base.$_3e_3d,[$UHC.$Base.$Ord__DCT74__58__0,$c,48]);
          return new _A_($UHC.$Base.$_26_26,[$__3,$__]);});
$UHC.$Base.$isHexDigit=
 new _F_(function($c)
         {var $__=
           new _A_($UHC.$Base.$_3c_3d,[$UHC.$Base.$Ord__DCT74__58__0,$c,102]);
          var $__3=
           new _A_($UHC.$Base.$_3e_3d,[$UHC.$Base.$Ord__DCT74__58__0,$c,97]);
          var $__4=
           new _A_($UHC.$Base.$_26_26,[$__3,$__]);
          var $__5=
           new _A_($UHC.$Base.$_3c_3d,[$UHC.$Base.$Ord__DCT74__58__0,$c,70]);
          var $__6=
           new _A_($UHC.$Base.$_3e_3d,[$UHC.$Base.$Ord__DCT74__58__0,$c,65]);
          var $__7=
           new _A_($UHC.$Base.$_26_26,[$__6,$__5]);
          var $__8=
           new _A_($UHC.$Base.$_7c_7c,[$__7,$__4]);
          var $__9=
           new _A_($UHC.$Base.$isDigit,[$c]);
          return new _A_($UHC.$Base.$_7c_7c,[$__9,$__8]);});
$UHC.$Base.$prefixUNQ7643=
 new _F_(function($c,$__)
         {var $__3=
           _e_($__);
          var $__6=
           new _A_($UHC.$Base.$_3a,[$c,$__3[0]]);
          var $__7=
           [$__6,$__3[1]];
          return $__7;});
$UHC.$Base.$cNEW4807UNQ7683CCN=
 new _F_(function($table,$__,$s,$c)
         {var $__5=
           new _A_($UHC.$Base.$__76__32620__0NEW4812UNQ7684CCN,[$table,$__,$c]);
          var $c6=
           _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,94,$c]));
          var $__swJSW419__0;
          switch($c6._tag_)
           {case 0:
             var $c7=
              _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,111,$c]));
             var $__swJSW420__0;
             switch($c7._tag_)
              {case 0:
                var $c8=
                 _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,120,$c]));
                var $__swJSW421__0;
                switch($c8._tag_)
                 {case 0:
                   $__swJSW421__0=
                    $__5;
                   break;
                  case 1:
                   var $__9=
                    new _A_($UHC.$Base.$span,[$UHC.$Base.$isHexDigit,$s]);
                   var $__10=
                    new _A_($UHC.$Base.$prefixUNQ7643,[120,$__9]);
                   var $__11=
                    new _A_($UHC.$Base.$_3a,[$__10,$UHC.$Base.$_5b_5d]);
                   $__swJSW421__0=
                    $__11;
                   break;}
                $__swJSW420__0=
                 $__swJSW421__0;
                break;
               case 1:
                var $__12=
                 new _A_($UHC.$Base.$span,[$UHC.$Base.$isOctDigit,$s]);
                var $__13=
                 new _A_($UHC.$Base.$prefixUNQ7643,[111,$__12]);
                var $__14=
                 new _A_($UHC.$Base.$_3a,[$__13,$UHC.$Base.$_5b_5d]);
                $__swJSW420__0=
                 $__14;
                break;}
             $__swJSW419__0=
              $__swJSW420__0;
             break;
            case 1:
             var $s15=
              _e_($s);
             var $__swJSW422__0;
             switch($s15._tag_)
              {case 0:
                var $__18=
                 new _A_($UHC.$Base.$_3c_3d,[$UHC.$Base.$Ord__DCT74__58__0,$s15._1,95]);
                var $__19=
                 new _A_($UHC.$Base.$_3e_3d,[$UHC.$Base.$Ord__DCT74__58__0,$s15._1,64]);
                var $__20=
                 new _A_($UHC.$Base.$_26_26,[$__19,$__18]);
                var $__21=
                 _e_($__20);
                var $__swJSW423__0;
                switch($__21._tag_)
                 {case 0:
                   $__swJSW423__0=
                    $__5;
                   break;
                  case 1:
                   var $__22=
                    new _A_($UHC.$Base.$_3a,[$s15._1,$UHC.$Base.$_5b_5d]);
                   var $__23=
                    new _A_($UHC.$Base.$_3a,[94,$__22]);
                   var $__24=
                    [$__23,$s15._2];
                   var $__25=
                    new _A_($UHC.$Base.$_3a,[$__24,$UHC.$Base.$_5b_5d]);
                   $__swJSW423__0=
                    $__25;
                   break;}
                $__swJSW422__0=
                 $__swJSW423__0;
                break;
               case 1:
                $__swJSW422__0=
                 $__5;
                break;}
             $__swJSW419__0=
              $__swJSW422__0;
             break;}
          return $__swJSW419__0;});
$UHC.$Base.$lexEscUNQ7650=
 new _F_(function($table,$x1)
         {var $__=
           _e_($x1);
          var $__swJSW424__0;
          switch($__._tag_)
           {case 0:
             var $c6=
              new _A_($UHC.$Base.$cNEW4807UNQ7683CCN,[$table,$__,$__._2,$__._1]);
             var $__7=
              new _A_($UHC.$Base.$packedStringToString,["abfnrtv\\\"'"]);
             var $__8=
              new _A_($UHC.$Base.$elem,[$UHC.$Base.$Eq__DCT74__56__0,$__._1,$__7]);
             var $__9=
              _e_($__8);
             var $__swJSW425__0;
             switch($__9._tag_)
              {case 0:
                $__swJSW425__0=
                 $c6;
                break;
               case 1:
                var $__10=
                 new _A_($UHC.$Base.$_3a,[$__._1,$UHC.$Base.$_5b_5d]);
                var $__11=
                 [$__10,$__._2];
                var $__12=
                 new _A_($UHC.$Base.$_3a,[$__11,$UHC.$Base.$_5b_5d]);
                $__swJSW425__0=
                 $__12;
                break;}
             $__swJSW424__0=
              $__swJSW425__0;
             break;
            case 1:
             $__swJSW424__0=
              $UHC.$Base.$_5b_5d;
             break;}
          return $__swJSW424__0;});
$UHC.$Base.$lexLitChar=
 new _F_(function($x1)
         {var $__=
           _e_($x1);
          var $__swJSW426__0;
          switch($__._tag_)
           {case 0:
             var $__5=
              new _A_($UHC.$Base.$packedStringToString,["DEL"]);
             var $__6=
              [127,$__5];
             var $table=
              new _A_($UHC.$Base.$_3a,[$__6,$UHC.$Base.$asciiTab]);
             var $__8=
              new _A_($UHC.$Base.$_2f_3d,[$UHC.$Base.$Eq__DCT74__56__0,$__._1,92]);
             var $__9=
              _e_($__8);
             var $__swJSW427__0;
             switch($__9._tag_)
              {case 0:
                var $__10=
                 _e_($UHC.$Base.$otherwise);
                var $__swJSW428__0;
                switch($__10._tag_)
                 {case 0:
                   $__swJSW428__0=
                    $UHC.$Base.$undefined;
                   break;
                  case 1:
                   var $__11=
                    new _A_($UHC.$Base.$lexEscUNQ7650,[$table,$__._2]);
                   var $__12=
                    new _A_($UHC.$Base.$prefixUNQ7643,[92]);
                   var $__13=
                    new _A_($UHC.$Base.$map,[$__12,$__11]);
                   $__swJSW428__0=
                    $__13;
                   break;}
                $__swJSW427__0=
                 $__swJSW428__0;
                break;
               case 1:
                var $__14=
                 new _A_($UHC.$Base.$_3a,[$__._1,$UHC.$Base.$_5b_5d]);
                var $__15=
                 [$__14,$__._2];
                var $__16=
                 new _A_($UHC.$Base.$_3a,[$__15,$UHC.$Base.$_5b_5d]);
                $__swJSW427__0=
                 $__16;
                break;}
             $__swJSW426__0=
              $__swJSW427__0;
             break;
            case 1:
             $__swJSW426__0=
              $UHC.$Base.$_5b_5d;
             break;}
          return $__swJSW426__0;});
$UHC.$Base.$pNEW1799UNQ3626CCN=
 new _F_(function($x1,$x2)
         {var $x23=
           _e_($x2);
          var $__swJSW429__0;
          switch($x23._tag_)
           {case 0:
             var $__=
              new _A_($UHC.$Base.$span,[$x1,$x23._2]);
             var $zs=
              new _A_($UHC.$Base.$zsNEW1804UNQ3636,[$__]);
             var $ys=
              new _A_($UHC.$Base.$ysNEW1807UNQ3635,[$__]);
             var $__9=
              new _A_($x1,[$x23._1]);
             var $__10=
              _e_($__9);
             var $__swJSW430__0;
             switch($__10._tag_)
              {case 0:
                var $__11=
                 _e_($UHC.$Base.$otherwise);
                var $__swJSW431__0;
                switch($__11._tag_)
                 {case 0:
                   $__swJSW431__0=
                    $UHC.$Base.$undefined;
                   break;
                  case 1:
                   var $__12=
                    [$UHC.$Base.$_5b_5d,$x23];
                   $__swJSW431__0=
                    $__12;
                   break;}
                $__swJSW430__0=
                 $__swJSW431__0;
                break;
               case 1:
                var $__13=
                 new _A_($UHC.$Base.$_3a,[$x23._1,$ys]);
                var $__14=
                 [$__13,$zs];
                $__swJSW430__0=
                 $__14;
                break;}
             $__swJSW429__0=
              $__swJSW430__0;
             break;
            case 1:
             $__swJSW429__0=
              $UHC.$Base.$undefined;
             break;}
          return $__swJSW429__0;});
$UHC.$Base.$zsNEW1804UNQ3636=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return $__2[1];});
$UHC.$Base.$ysNEW1807UNQ3635=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return $__2[0];});
$UHC.$Base.$span=
 new _F_(function($x1,$x2)
         {var $p=
           new _A_($UHC.$Base.$pNEW1799UNQ3626CCN,[$x1,$x2]);
          var $x24=
           _e_($x2);
          var $__swJSW434__0;
          switch($x24._tag_)
           {case 0:
             $__swJSW434__0=
              $p;
             break;
            case 1:
             var $__=
              [$UHC.$Base.$_5b_5d,$UHC.$Base.$_5b_5d];
             $__swJSW434__0=
              $__;
             break;}
          return $__swJSW434__0;});
$UHC.$Base.$_24okUNQ3658=
 new _F_(function($_24x)
         {var $__=
           _e_($_24x);
          var $cs5=
           _e_($__[0]);
          var $__swJSW436__0;
          switch($cs5._tag_)
           {case 0:
             var $__8=
              [$cs5,$__[1]];
             var $__9=
              new _A_($UHC.$Base.$_3a,[$__8,$UHC.$Base.$_5b_5d]);
             $__swJSW436__0=
              $__9;
             break;
            case 1:
             $__swJSW436__0=
              $UHC.$Base.$_5b_5d;
             break;}
          return $__swJSW436__0;});
$UHC.$Base.$nonnull=
 new _F_(function($p,$s)
         {var $__=
           new _A_($UHC.$Base.$span,[$p,$s]);
          var $__4=
           new _A_($UHC.$Base.$_3a,[$__,$UHC.$Base.$_5b_5d]);
          return new _A_($UHC.$Base.$concatMap,[$UHC.$Base.$_24okUNQ3658,$__4]);});
$UHC.$Base.$lexDigits=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$nonnull,[$UHC.$Base.$isDigit]);}),[]);
$UHC.$Base.$foldr=
 new _F_(function($x1,$x2,$x3)
         {var $x34=
           _e_($x3);
          var $__swJSW437__0;
          switch($x34._tag_)
           {case 0:
             var $__=
              new _A_($UHC.$Base.$foldr,[$x1,$x2,$x34._2]);
             var $__8=
              new _A_($x1,[$x34._1,$__]);
             $__swJSW437__0=
              $__8;
             break;
            case 1:
             $__swJSW437__0=
              $x2;
             break;}
          return $__swJSW437__0;});
$UHC.$Base.$_7c_7c=
 new _F_(function($x1,$x2)
         {var $x13=
           _e_($x1);
          var $__swJSW438__0;
          switch($x13._tag_)
           {case 0:
             $__swJSW438__0=
              $x2;
             break;
            case 1:
             $__swJSW438__0=
              $UHC.$Base.$True__;
             break;}
          return $__swJSW438__0;});
$UHC.$Base.$or=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$foldr,[$UHC.$Base.$_7c_7c,$UHC.$Base.$False__]);}),[]);
$UHC.$Base.$any=
 new _F_(function($p)
         {var $__=
           new _A_($UHC.$Base.$map,[$p]);
          return new _A_($UHC.$Base.$_2e,[$UHC.$Base.$or,$__]);});
$UHC.$Base.$elem=
 new _F_(function($__)
         {var $__2=
           new _A_($UHC.$Base.$_3d_3d,[$__]);
          return new _A_($UHC.$Base.$_2e,[$UHC.$Base.$any,$__2]);});
$UHC.$Base.$_3e_3d=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._4;});
$UHC.$Base.$__76__19336__2__0NEW2115UNQ5002=
 new _F_(function($Ord__)
         {var $Eq__=
           _e_($Ord__);
          return $Eq__._5;});
$UHC.$Base.$Ord__CLS74__5__0DFLUHC_2eBase_2emin=
 new _F_(function($Ord__,$x,$y)
         {var $__=
           new _A_($UHC.$Base.$_3c_3d,[$Ord__,$x,$y]);
          var $__5=
           _e_($__);
          var $__swJSW441__0;
          switch($__5._tag_)
           {case 0:
             var $__6=
              _e_($UHC.$Base.$otherwise);
             var $__swJSW442__0;
             switch($__6._tag_)
              {case 0:
                var $__7=
                 new _A_($UHC.$Base.$packedStringToString,["FAIL 75_19_0"]);
                var $__8=
                 new _A_($UHC.$Base.$error,[$__7]);
                $__swJSW442__0=
                 $__8;
                break;
               case 1:
                $__swJSW442__0=
                 $y;
                break;}
             $__swJSW441__0=
              $__swJSW442__0;
             break;
            case 1:
             $__swJSW441__0=
              $x;
             break;}
          return $__swJSW441__0;});
$UHC.$Base.$Ord__CLS74__5__0DFLUHC_2eBase_2emax=
 new _F_(function($Ord__,$x,$y)
         {var $__=
           new _A_($UHC.$Base.$_3c_3d,[$Ord__,$x,$y]);
          var $__5=
           _e_($__);
          var $__swJSW443__0;
          switch($__5._tag_)
           {case 0:
             var $__6=
              _e_($UHC.$Base.$otherwise);
             var $__swJSW444__0;
             switch($__6._tag_)
              {case 0:
                var $__7=
                 new _A_($UHC.$Base.$packedStringToString,["FAIL 75_18_0"]);
                var $__8=
                 new _A_($UHC.$Base.$error,[$__7]);
                $__swJSW444__0=
                 $__8;
                break;
               case 1:
                $__swJSW444__0=
                 $x;
                break;}
             $__swJSW443__0=
              $__swJSW444__0;
             break;
            case 1:
             $__swJSW443__0=
              $y;
             break;}
          return $__swJSW443__0;});
$UHC.$Base.$Ord__CLS74__5__0DFLUHC_2eBase_2e_3c=
 new _F_(function($Ord__,$x,$y)
         {var $__=
           new _A_($UHC.$Base.$compare,[$Ord__,$x,$y]);
          return new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$__74__80__0,$__,$UHC.$Base.$LT__]);});
$UHC.$Base.$Ord__CLS74__5__0DFLUHC_2eBase_2e_3e=
 new _F_(function($Ord__,$x,$y)
         {var $__=
           new _A_($UHC.$Base.$compare,[$Ord__,$x,$y]);
          return new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$__74__80__0,$__,$UHC.$Base.$GT__]);});
$UHC.$Base.$_3c_3d=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._2;});
$UHC.$Base.$Ord__CLS74__5__0DFLUHC_2eBase_2ecompare=
 new _F_(function($__,$Ord__,$x,$y)
         {var $__5=
           new _A_($UHC.$Base.$_3d_3d,[$__,$x,$y]);
          var $__6=
           _e_($__5);
          var $__swJSW446__0;
          switch($__6._tag_)
           {case 0:
             var $__7=
              new _A_($UHC.$Base.$_3c_3d,[$Ord__,$x,$y]);
             var $__8=
              _e_($__7);
             var $__swJSW447__0;
             switch($__8._tag_)
              {case 0:
                var $__9=
                 _e_($UHC.$Base.$otherwise);
                var $__swJSW448__0;
                switch($__9._tag_)
                 {case 0:
                   var $__10=
                    new _A_($UHC.$Base.$packedStringToString,["FAIL 75_13_0"]);
                   var $__11=
                    new _A_($UHC.$Base.$error,[$__10]);
                   $__swJSW448__0=
                    $__11;
                   break;
                  case 1:
                   $__swJSW448__0=
                    $UHC.$Base.$GT__;
                   break;}
                $__swJSW447__0=
                 $__swJSW448__0;
                break;
               case 1:
                $__swJSW447__0=
                 $UHC.$Base.$LT__;
                break;}
             $__swJSW446__0=
              $__swJSW447__0;
             break;
            case 1:
             $__swJSW446__0=
              $UHC.$Base.$EQ__;
             break;}
          return $__swJSW446__0;});
$UHC.$Base.$Ord__CLS74__5__0DFLUHC_2eBase_2e_3c_3d=
 new _F_(function($Ord__,$x,$y)
         {var $__=
           new _A_($UHC.$Base.$compare,[$Ord__,$x,$y]);
          return new _A_($UHC.$Base.$_2f_3d,[$UHC.$Base.$__74__80__0,$__,$UHC.$Base.$GT__]);});
$UHC.$Base.$compare=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._6;});
$UHC.$Base.$__74__80__0NEW1861UNQ9905EVLRDC=
 new _F_(function($__,$__2)
         {var $Eq__=
           _e_(new _A_($UHC.$Base.$Eq__CLS74__4__0,[$__]));
          var $__6=
           {_tag_:0,_1:$Eq__._1,_2:$__2};
          return $__6;});
$UHC.$Base.$__74__80__0NEW1858UNQ9894RDC=
 new _F_(function($__,$__2)
         {var $__3=
           new _A_($UHC.$Base.$__74__80__0NEW1861UNQ9905EVLRDC,[$__,$__2]);
          return $__3;});
$UHC.$Base.$GT__=
 new _A_(new _F_(function()
                 {return {_tag_:1};}),[]);
$UHC.$Base.$EQ__=
 new _A_(new _F_(function()
                 {return {_tag_:0};}),[]);
$UHC.$Base.$LT__=
 new _A_(new _F_(function()
                 {return {_tag_:2};}),[]);
$UHC.$Base.$__Rep0OrderingDFLUHC_2eBase_2eto0GENRepresentable0=
 new _F_(function($proj__1)
         {var $proj__2=
           _e_($proj__1);
          var $__swJSW451__0;
          switch($proj__2._tag_)
           {case 0:
             var $proj__4=
              _e_($proj__2.unL1);
             $__swJSW451__0=
              $UHC.$Base.$LT__;
             break;
            case 1:
             var $proj__56=
              _e_($proj__2.unR1);
             var $__swJSW453__0;
             switch($proj__56._tag_)
              {case 0:
                var $proj__7=
                 _e_($proj__56.unL1);
                $__swJSW453__0=
                 $UHC.$Base.$EQ__;
                break;
               case 1:
                var $proj__9=
                 _e_($proj__56.unR1);
                $__swJSW453__0=
                 $UHC.$Base.$GT__;
                break;}
             $__swJSW451__0=
              $__swJSW453__0;
             break;}
          return $__swJSW451__0;});
$UHC.$Base.$__Rep0OrderingDFLUHC_2eBase_2efrom0GENRepresentable0=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          var $__swJSW456__0;
          switch($x2._tag_)
           {case 0:
             var $__=
              new _A_($UHC.$Base.$M1__,[$UHC.$Base.$U1__]);
             var $__4=
              new _A_($UHC.$Base.$L1__,[$__]);
             var $__5=
              new _A_($UHC.$Base.$R1__,[$__4]);
             var $__6=
              new _A_($UHC.$Base.$M1__,[$__5]);
             $__swJSW456__0=
              $__6;
             break;
            case 1:
             var $__=
              new _A_($UHC.$Base.$M1__,[$UHC.$Base.$U1__]);
             var $__8=
              new _A_($UHC.$Base.$R1__,[$__]);
             var $__9=
              new _A_($UHC.$Base.$R1__,[$__8]);
             var $__10=
              new _A_($UHC.$Base.$M1__,[$__9]);
             $__swJSW456__0=
              $__10;
             break;
            case 2:
             var $__=
              new _A_($UHC.$Base.$M1__,[$UHC.$Base.$U1__]);
             var $__12=
              new _A_($UHC.$Base.$L1__,[$__]);
             var $__13=
              new _A_($UHC.$Base.$M1__,[$__12]);
             $__swJSW456__0=
              $__13;
             break;}
          return $__swJSW456__0;});
$UHC.$Base.$__Rep0OrderingNEW1319UNQ2261EVLSDCGENRepresentable0=
 new _F_(function($__)
         {var $Representable0__=
           _e_(new _A_($UHC.$Base.$Representable0__CLS74__369__0,[$__]));
          var $__5=
           {_tag_:0,_1:$UHC.$Base.$__Rep0OrderingDFLUHC_2eBase_2efrom0GENRepresentable0,_2:$UHC.$Base.$__Rep0OrderingDFLUHC_2eBase_2eto0GENRepresentable0};
          return $__5;});
$UHC.$Base.$__Rep0OrderingNEW1317UNQ2260SDCGENRepresentable0=
 new _F_(function($__)
         {var $__2=
           new _A_($UHC.$Base.$__Rep0OrderingNEW1319UNQ2261EVLSDCGENRepresentable0,[$__]);
          return $__2;});
$UHC.$Base.$__Rep0OrderingUNQ2260SDCGENRepresentable0=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$__Rep0OrderingNEW1317UNQ2260SDCGENRepresentable0,[$UHC.$Base.$__Rep0OrderingUNQ2260SDCGENRepresentable0]);}),[]);
$UHC.$Base.$__Rep0OrderingGENRepresentable0=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$__Rep0OrderingUNQ2260SDCGENRepresentable0;}),[]);
$UHC.$Base.$__76__42802__2__5UNQ9895=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Eq_27__DCT74__392__0,[$UHC.$Base.$__76__42802__2__3UNQ9902,$UHC.$Base.$__76__42802__2__3UNQ9902]);}),[]);
$UHC.$Base.$__76__42802__2__3UNQ9902=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Eq_27__DCT74__391__0,[$UHC.$Base.$Eq_27__DCT74__389__0]);}),[]);
$UHC.$Base.$__76__42802__2__2UNQ9901=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Eq_27__DCT74__392__0,[$UHC.$Base.$__76__42802__2__3UNQ9902,$UHC.$Base.$__76__42802__2__5UNQ9895]);}),[]);
$UHC.$Base.$__76__42810__0__4__0UNQ9897=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Eq_27__DCT74__391__0,[$UHC.$Base.$__76__42802__2__2UNQ9901]);}),[]);
$UHC.$Base.$__74__80__0DFLUHC_2eBase_2e_3d_3d=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$geqdefault,[$UHC.$Base.$__Rep0OrderingGENRepresentable0,$UHC.$Base.$__76__42810__0__4__0UNQ9897,$UHC.$Base.$undefined]);}),[]);
$UHC.$Base.$__74__80__0UNQ9894RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$__74__80__0NEW1858UNQ9894RDC,[$UHC.$Base.$__74__80__0UNQ9894RDC,$UHC.$Base.$__74__80__0DFLUHC_2eBase_2e_3d_3d]);}),[]);
$UHC.$Base.$__74__80__0=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$__74__80__0UNQ9894RDC;}),[]);
$UHC.$Base.$Ord__CLS74__5__0DFLUHC_2eBase_2e_3e_3d=
 new _F_(function($Ord__,$x,$y)
         {var $__=
           new _A_($UHC.$Base.$compare,[$Ord__,$x,$y]);
          return new _A_($UHC.$Base.$_2f_3d,[$UHC.$Base.$__74__80__0,$__,$UHC.$Base.$LT__]);});
$UHC.$Base.$Ord__CLS74__5__0=
 new _F_(function($Ord__)
         {var $__=
           new _A_($UHC.$Base.$__76__19336__2__0NEW2115UNQ5002,[$Ord__]);
          var $__3=
           new _A_($UHC.$Base.$Ord__CLS74__5__0DFLUHC_2eBase_2emin,[$Ord__]);
          var $__4=
           new _A_($UHC.$Base.$Ord__CLS74__5__0DFLUHC_2eBase_2emax,[$Ord__]);
          var $__5=
           new _A_($UHC.$Base.$Ord__CLS74__5__0DFLUHC_2eBase_2ecompare,[$__,$Ord__]);
          var $__6=
           new _A_($UHC.$Base.$Ord__CLS74__5__0DFLUHC_2eBase_2e_3e_3d,[$Ord__]);
          var $__7=
           new _A_($UHC.$Base.$Ord__CLS74__5__0DFLUHC_2eBase_2e_3e,[$Ord__]);
          var $__8=
           new _A_($UHC.$Base.$Ord__CLS74__5__0DFLUHC_2eBase_2e_3c_3d,[$Ord__]);
          var $__9=
           new _A_($UHC.$Base.$Ord__CLS74__5__0DFLUHC_2eBase_2e_3c,[$Ord__]);
          var $Ord__10=
           {_tag_:0,_1:$__9,_2:$__8,_3:$__7,_4:$__6,_5:$UHC.$Base.$undefined,_6:$__5,_7:$__4,_8:$__3};
          return $Ord__10;});
$UHC.$Base.$primCmpChar=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__2);
          return primCmpInt($__3,$__4);});
$UHC.$Base.$Ord__NEW2187UNQ10858EVLDCT74__58__0RDC=
 new _F_(function($Ord__)
         {var $Ord__2=
           _e_(new _A_($UHC.$Base.$Ord__CLS74__5__0,[$Ord__]));
          var $__11=
           {_tag_:0,_1:$Ord__2._1,_2:$Ord__2._2,_3:$Ord__2._3,_4:$Ord__2._4,_5:$UHC.$Base.$Eq__DCT74__56__0,_6:$UHC.$Base.$primCmpChar,_7:$Ord__2._7,_8:$Ord__2._8};
          return $__11;});
$UHC.$Base.$Ord__NEW2185UNQ10857DCT74__58__0RDC=
 new _F_(function($Ord__)
         {var $Ord__2=
           new _A_($UHC.$Base.$Ord__NEW2187UNQ10858EVLDCT74__58__0RDC,[$Ord__]);
          return $Ord__2;});
$UHC.$Base.$Ord__UNQ10857DCT74__58__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Ord__NEW2185UNQ10857DCT74__58__0RDC,[$UHC.$Base.$Ord__UNQ10857DCT74__58__0RDC]);}),[]);
$UHC.$Base.$Ord__DCT74__58__0=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$Ord__UNQ10857DCT74__58__0RDC;}),[]);
$UHC.$Base.$isDigit=
 new _F_(function($c)
         {var $__=
           new _A_($UHC.$Base.$_3c_3d,[$UHC.$Base.$Ord__DCT74__58__0,$c,57]);
          var $__3=
           new _A_($UHC.$Base.$_3e_3d,[$UHC.$Base.$Ord__DCT74__58__0,$c,48]);
          return new _A_($UHC.$Base.$_26_26,[$__3,$__]);});
$UHC.$Base.$cNEW4871UNQ7768CCN=
 new _F_(function($s,$c)
         {var $__=
           new _A_($UHC.$Base.$__76__33435__0NEW4874UNQ7769CCN,[$s,$c]);
          var $c4=
           _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,34,$c]));
          var $__swJSW459__0;
          switch($c4._tag_)
           {case 0:
             var $c5=
              _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,39,$c]));
             var $__swJSW460__0;
             switch($c5._tag_)
              {case 0:
                $__swJSW460__0=
                 $__;
                break;
               case 1:
                var $__6=
                 new _A_($UHC.$Base.$Eq__DCT74__394__0,[$UHC.$Base.$Eq__DCT74__56__0]);
                var $__7=
                 new _A_($UHC.$Base.$lexLitChar,[$s]);
                var $__8=
                 new _A_($UHC.$Base.$_24okUNQ7977,[$__6]);
                $__swJSW460__0=
                 new _A_($UHC.$Base.$concatMap,[$__8,$__7]);
                break;}
             $__swJSW459__0=
              $__swJSW460__0;
             break;
            case 1:
             var $__9=
              new _A_($UHC.$Base.$lexStringUNQ8005,[$s]);
             $__swJSW459__0=
              new _A_($UHC.$Base.$concatMap,[$UHC.$Base.$_24okUNQ8006,$__9]);
             break;}
          return $__swJSW459__0;});
$UHC.$Base.$__76__33435__0NEW4874UNQ7769CCN=
 new _F_(function($s,$c)
         {var $__=
           new _A_($UHC.$Base.$isSymUNQ7773,[$c]);
          var $__4=
           _e_($__);
          var $__swJSW461__0;
          switch($__4._tag_)
           {case 0:
             var $__5=
              new _A_($UHC.$Base.$isAlpha,[$c]);
             var $__6=
              _e_($__5);
             var $__swJSW462__0;
             switch($__6._tag_)
              {case 0:
                var $__7=
                 new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,$c,95]);
                var $__8=
                 _e_($__7);
                var $__swJSW463__0;
                switch($__8._tag_)
                 {case 0:
                   var $__9=
                    new _A_($UHC.$Base.$isSingleUNQ7777,[$c]);
                   var $__10=
                    _e_($__9);
                   var $__swJSW464__0;
                   switch($__10._tag_)
                    {case 0:
                      var $__11=
                       new _A_($UHC.$Base.$isDigit,[$c]);
                      var $__12=
                       _e_($__11);
                      var $__swJSW465__0;
                      switch($__12._tag_)
                       {case 0:
                         var $__13=
                          _e_($UHC.$Base.$otherwise);
                         var $__swJSW466__0;
                         switch($__13._tag_)
                          {case 0:
                            $__swJSW466__0=
                             $UHC.$Base.$undefined;
                            break;
                           case 1:
                            $__swJSW466__0=
                             $UHC.$Base.$_5b_5d;
                            break;}
                         $__swJSW465__0=
                          $__swJSW466__0;
                         break;
                        case 1:
                         var $__14=
                          new _A_($UHC.$Base.$span,[$UHC.$Base.$isDigit,$s]);
                         var $__15=
                          new _A_($UHC.$Base.$_3a,[$__14,$UHC.$Base.$_5b_5d]);
                         var $__16=
                          new _A_($UHC.$Base.$_24okUNQ7898,[$c]);
                         $__swJSW465__0=
                          new _A_($UHC.$Base.$concatMap,[$__16,$__15]);
                         break;}
                      $__swJSW464__0=
                       $__swJSW465__0;
                      break;
                     case 1:
                      var $__17=
                       new _A_($UHC.$Base.$_3a,[$c,$UHC.$Base.$_5b_5d]);
                      var $__18=
                       [$__17,$s];
                      var $__19=
                       new _A_($UHC.$Base.$_3a,[$__18,$UHC.$Base.$_5b_5d]);
                      $__swJSW464__0=
                       $__19;
                      break;}
                   $__swJSW463__0=
                    $__swJSW464__0;
                   break;
                  case 1:
                   var $__20=
                    new _A_($UHC.$Base.$span,[$UHC.$Base.$isIdCharUNQ7781,$s]);
                   var $__21=
                    _e_($__20);
                   var $__24=
                    new _A_($UHC.$Base.$_3a,[$c,$__21[0]]);
                   var $__25=
                    [$__24,$__21[1]];
                   var $__26=
                    new _A_($UHC.$Base.$_3a,[$__25,$UHC.$Base.$_5b_5d]);
                   var $__27=
                    _e_($__21[0]);
                   var $__swJSW468__0;
                   switch($__27._tag_)
                    {case 0:
                      $__swJSW468__0=
                       $__26;
                      break;
                     case 1:
                      var $__30=
                       new _A_($UHC.$Base.$_3a,[$c,$UHC.$Base.$_5b_5d]);
                      var $__31=
                       [$__30,$s];
                      var $__32=
                       new _A_($UHC.$Base.$_3a,[$__31,$UHC.$Base.$_5b_5d]);
                      $__swJSW468__0=
                       $__32;
                      break;}
                   $__swJSW463__0=
                    $__swJSW468__0;
                   break;}
                $__swJSW462__0=
                 $__swJSW463__0;
                break;
               case 1:
                var $__33=
                 new _A_($UHC.$Base.$span,[$UHC.$Base.$isIdCharUNQ7781,$s]);
                var $__34=
                 new _A_($UHC.$Base.$_3a,[$__33,$UHC.$Base.$_5b_5d]);
                var $__35=
                 new _A_($UHC.$Base.$_24okUNQ7939,[$c]);
                $__swJSW462__0=
                 new _A_($UHC.$Base.$concatMap,[$__35,$__34]);
                break;}
             $__swJSW461__0=
              $__swJSW462__0;
             break;
            case 1:
             var $__36=
              new _A_($UHC.$Base.$span,[$UHC.$Base.$isSymUNQ7773,$s]);
             var $__37=
              new _A_($UHC.$Base.$_3a,[$__36,$UHC.$Base.$_5b_5d]);
             var $__38=
              new _A_($UHC.$Base.$_24okUNQ7955,[$c]);
             $__swJSW461__0=
              new _A_($UHC.$Base.$concatMap,[$__38,$__37]);
             break;}
          return $__swJSW461__0;});
$UHC.$Base.$isSymUNQ7773=
 new _F_(function($c)
         {var $__=
           new _A_($UHC.$Base.$packedStringToString,["!@#$%&*+./<=>?\\^|:-~"]);
          return new _A_($UHC.$Base.$elem,[$UHC.$Base.$Eq__DCT74__56__0,$c,$__]);});
$UHC.$Base.$isSingleUNQ7777=
 new _F_(function($c)
         {var $__=
           new _A_($UHC.$Base.$packedStringToString,[",;()[]{}_`"]);
          return new _A_($UHC.$Base.$elem,[$UHC.$Base.$Eq__DCT74__56__0,$c,$__]);});
$UHC.$Base.$lexExpUNQ7775=
 new _F_(function($x1)
         {var $__=
           new _A_($UHC.$Base.$packedStringToString,[""]);
          var $__3=
           [$__,$x1];
          var $__4=
           new _A_($UHC.$Base.$_3a,[$__3,$UHC.$Base.$_5b_5d]);
          var $__5=
           _e_($x1);
          var $__swJSW469__0;
          switch($__5._tag_)
           {case 0:
             var $__8=
              new _A_($UHC.$Base.$packedStringToString,["eE"]);
             var $__9=
              new _A_($UHC.$Base.$elem,[$UHC.$Base.$Eq__DCT74__56__0,$__5._1,$__8]);
             var $__10=
              _e_($__9);
             var $__swJSW470__0;
             switch($__10._tag_)
              {case 0:
                $__swJSW470__0=
                 $__4;
                break;
               case 1:
                var $__11=
                 new _A_($UHC.$Base.$__78__9635NEW4889,[$__5._1,$__5._2]);
                var $__12=
                 new _A_($UHC.$Base.$__78__9603NEW4898,[$__5._1,$__5._2]);
                var $__13=
                 new _A_($UHC.$Base.$_2b_2b,[$__12,$__11]);
                $__swJSW470__0=
                 $__13;
                break;}
             $__swJSW469__0=
              $__swJSW470__0;
             break;
            case 1:
             $__swJSW469__0=
              $__4;
             break;}
          return $__swJSW469__0;});
$UHC.$Base.$__78__9635NEW4889=
 new _F_(function($e,$s)
         {var $__=
           new _A_($UHC.$Base.$lexDigits,[$s]);
          var $__4=
           new _A_($UHC.$Base.$_24okUNQ7824,[$e]);
          return new _A_($UHC.$Base.$concatMap,[$__4,$__]);});
$UHC.$Base.$_24okUNQ7824=
 new _F_(function($e,$_24x)
         {var $__=
           _e_($_24x);
          var $__6=
           new _A_($UHC.$Base.$_3a,[$e,$__[0]]);
          var $__7=
           [$__6,$__[1]];
          var $__8=
           new _A_($UHC.$Base.$_3a,[$__7,$UHC.$Base.$_5b_5d]);
          return $__8;});
$UHC.$Base.$__78__9603NEW4898=
 new _F_(function($e,$s)
         {var $__=
           new _A_($UHC.$Base.$_3a,[$s,$UHC.$Base.$_5b_5d]);
          var $__4=
           new _A_($UHC.$Base.$_24okUNQ7798,[$e]);
          return new _A_($UHC.$Base.$concatMap,[$__4,$__]);});
$UHC.$Base.$_24okUNQ7798=
 new _F_(function($e,$_24x)
         {var $__=
           _e_($_24x);
          var $__swJSW472__0;
          switch($__._tag_)
           {case 0:
             var $__6=
              new _A_($UHC.$Base.$packedStringToString,["+-"]);
             var $__7=
              new _A_($UHC.$Base.$elem,[$UHC.$Base.$Eq__DCT74__56__0,$__._1,$__6]);
             var $__8=
              _e_($__7);
             var $__swJSW473__0;
             switch($__8._tag_)
              {case 0:
                $__swJSW473__0=
                 $UHC.$Base.$_5b_5d;
                break;
               case 1:
                var $__9=
                 new _A_($UHC.$Base.$lexDigits,[$__._2]);
                var $__10=
                 new _A_($UHC.$Base.$_24okUNQ7808,[$e,$__._1]);
                $__swJSW473__0=
                 new _A_($UHC.$Base.$concatMap,[$__10,$__9]);
                break;}
             $__swJSW472__0=
              $__swJSW473__0;
             break;
            case 1:
             $__swJSW472__0=
              $UHC.$Base.$_5b_5d;
             break;}
          return $__swJSW472__0;});
$UHC.$Base.$_24okUNQ7808=
 new _F_(function($e,$c,$_24x)
         {var $__=
           _e_($_24x);
          var $__7=
           new _A_($UHC.$Base.$_3a,[$c,$__[0]]);
          var $__8=
           new _A_($UHC.$Base.$_3a,[$e,$__7]);
          var $__9=
           [$__8,$__[1]];
          var $__10=
           new _A_($UHC.$Base.$_3a,[$__9,$UHC.$Base.$_5b_5d]);
          return $__10;});
$UHC.$Base.$lexFracExpUNQ7779=
 new _F_(function($x1)
         {var $__=
           new _A_($UHC.$Base.$lexExpUNQ7775,[$x1]);
          var $__3=
           _e_($x1);
          var $__swJSW475__0;
          switch($__3._tag_)
           {case 0:
             var $__6=
              _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,46,$__3._1]));
             var $__swJSW476__0;
             switch($__6._tag_)
              {case 0:
                $__swJSW476__0=
                 $__;
                break;
               case 1:
                var $__7=
                 _e_($__3._2);
                var $__swJSW477__0;
                switch($__7._tag_)
                 {case 0:
                   var $__10=
                    new _A_($UHC.$Base.$isDigit,[$__7._1]);
                   var $__11=
                    _e_($__10);
                   var $__swJSW478__0;
                   switch($__11._tag_)
                    {case 0:
                      $__swJSW478__0=
                       $__;
                      break;
                     case 1:
                      var $__12=
                       new _A_($UHC.$Base.$_3a,[$__7._1,$__7._2]);
                      var $__13=
                       new _A_($UHC.$Base.$lexDigits,[$__12]);
                      $__swJSW478__0=
                       new _A_($UHC.$Base.$concatMap,[$UHC.$Base.$_24okUNQ7856,$__13]);
                      break;}
                   $__swJSW477__0=
                    $__swJSW478__0;
                   break;
                  case 1:
                   $__swJSW477__0=
                    $__;
                   break;}
                $__swJSW476__0=
                 $__swJSW477__0;
                break;}
             $__swJSW475__0=
              $__swJSW476__0;
             break;
            case 1:
             $__swJSW475__0=
              $__;
             break;}
          return $__swJSW475__0;});
$UHC.$Base.$_24okUNQ7856=
 new _F_(function($_24x)
         {var $__=
           _e_($_24x);
          var $__5=
           new _A_($UHC.$Base.$lexExpUNQ7775,[$__[1]]);
          var $__6=
           new _A_($UHC.$Base.$_24okUNQ7869,[$__[0]]);
          return new _A_($UHC.$Base.$concatMap,[$__6,$__5]);});
$UHC.$Base.$_24okUNQ7869=
 new _F_(function($ds,$_24x)
         {var $__=
           _e_($_24x);
          var $__6=
           new _A_($UHC.$Base.$_2b_2b,[$ds,$__[0]]);
          var $__7=
           new _A_($UHC.$Base.$_3a,[46,$__6]);
          var $__8=
           [$__7,$__[1]];
          var $__9=
           new _A_($UHC.$Base.$_3a,[$__8,$UHC.$Base.$_5b_5d]);
          return $__9;});
$UHC.$Base.$isIdCharUNQ7781=
 new _F_(function($c)
         {var $__=
           new _A_($UHC.$Base.$packedStringToString,["_'"]);
          var $__3=
           new _A_($UHC.$Base.$elem,[$UHC.$Base.$Eq__DCT74__56__0,$c,$__]);
          var $__4=
           new _A_($UHC.$Base.$isAlphaNum,[$c]);
          return new _A_($UHC.$Base.$_7c_7c,[$__4,$__3]);});
$UHC.$Base.$_24okUNQ7898=
 new _F_(function($c,$_24x)
         {var $__=
           _e_($_24x);
          var $__6=
           new _A_($UHC.$Base.$lexFracExpUNQ7779,[$__[1]]);
          var $__7=
           new _A_($UHC.$Base.$_24okUNQ7911,[$c,$__[0]]);
          return new _A_($UHC.$Base.$concatMap,[$__7,$__6]);});
$UHC.$Base.$_24okUNQ7911=
 new _F_(function($c,$ds,$_24x)
         {var $__=
           _e_($_24x);
          var $__7=
           new _A_($UHC.$Base.$_2b_2b,[$ds,$__[0]]);
          var $__8=
           new _A_($UHC.$Base.$_3a,[$c,$__7]);
          var $__9=
           [$__8,$__[1]];
          var $__10=
           new _A_($UHC.$Base.$_3a,[$__9,$UHC.$Base.$_5b_5d]);
          return $__10;});
$UHC.$Base.$_24okUNQ7939=
 new _F_(function($c,$_24x)
         {var $__=
           _e_($_24x);
          var $__6=
           new _A_($UHC.$Base.$_3a,[$c,$__[0]]);
          var $__7=
           [$__6,$__[1]];
          var $__8=
           new _A_($UHC.$Base.$_3a,[$__7,$UHC.$Base.$_5b_5d]);
          return $__8;});
$UHC.$Base.$_24okUNQ7955=
 new _F_(function($c,$_24x)
         {var $__=
           _e_($_24x);
          var $__6=
           new _A_($UHC.$Base.$_3a,[$c,$__[0]]);
          var $__7=
           [$__6,$__[1]];
          var $__8=
           new _A_($UHC.$Base.$_3a,[$__7,$UHC.$Base.$_5b_5d]);
          return $__8;});
$UHC.$Base.$_24okUNQ7977=
 new _F_(function($__,$_24x)
         {var $__3=
           _e_($_24x);
          var $__6=
           _e_($__3[1]);
          var $__swJSW486__0;
          switch($__6._tag_)
           {case 0:
             var $__9=
              _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,39,$__6._1]));
             var $__swJSW487__0;
             switch($__9._tag_)
              {case 0:
                $__swJSW487__0=
                 $UHC.$Base.$_5b_5d;
                break;
               case 1:
                var $__10=
                 new _A_($UHC.$Base.$packedStringToString,["'"]);
                var $__11=
                 new _A_($UHC.$Base.$_2f_3d,[$__,$__3[0],$__10]);
                var $__12=
                 _e_($__11);
                var $__swJSW488__0;
                switch($__12._tag_)
                 {case 0:
                   $__swJSW488__0=
                    $UHC.$Base.$_5b_5d;
                   break;
                  case 1:
                   var $__13=
                    new _A_($UHC.$Base.$packedStringToString,["'"]);
                   var $__14=
                    new _A_($UHC.$Base.$_2b_2b,[$__3[0],$__13]);
                   var $__15=
                    new _A_($UHC.$Base.$_3a,[39,$__14]);
                   var $__16=
                    [$__15,$__6._2];
                   var $__17=
                    new _A_($UHC.$Base.$_3a,[$__16,$UHC.$Base.$_5b_5d]);
                   $__swJSW488__0=
                    $__17;
                   break;}
                $__swJSW487__0=
                 $__swJSW488__0;
                break;}
             $__swJSW486__0=
              $__swJSW487__0;
             break;
            case 1:
             $__swJSW486__0=
              $UHC.$Base.$_5b_5d;
             break;}
          return $__swJSW486__0;});
$UHC.$Base.$_24okUNQ8006=
 new _F_(function($_24x)
         {var $__=
           _e_($_24x);
          var $__5=
           new _A_($UHC.$Base.$_3a,[34,$__[0]]);
          var $__6=
           [$__5,$__[1]];
          var $__7=
           new _A_($UHC.$Base.$_3a,[$__6,$UHC.$Base.$_5b_5d]);
          return $__7;});
$UHC.$Base.$lexStrItemUNQ8003=
 new _F_(function($x1)
         {var $__=
           new _A_($UHC.$Base.$lexLitChar,[$x1]);
          var $__3=
           _e_($x1);
          var $__swJSW490__0;
          switch($__3._tag_)
           {case 0:
             var $__6=
              _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,92,$__3._1]));
             var $__swJSW491__0;
             switch($__6._tag_)
              {case 0:
                $__swJSW491__0=
                 $__;
                break;
               case 1:
                var $__7=
                 _e_($__3._2);
                var $__swJSW492__0;
                switch($__7._tag_)
                 {case 0:
                   var $__10=
                    new _A_($UHC.$Base.$__76__33677__0NEW5011UNQ8021CCN,[$__,$__7._2,$__7._1]);
                   var $__11=
                    _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,38,$__7._1]));
                   var $__swJSW493__0;
                   switch($__11._tag_)
                    {case 0:
                      $__swJSW493__0=
                       $__10;
                      break;
                     case 1:
                      var $__12=
                       new _A_($UHC.$Base.$packedStringToString,["\\&"]);
                      var $__13=
                       [$__12,$__7._2];
                      var $__14=
                       new _A_($UHC.$Base.$_3a,[$__13,$UHC.$Base.$_5b_5d]);
                      $__swJSW493__0=
                       $__14;
                      break;}
                   $__swJSW492__0=
                    $__swJSW493__0;
                   break;
                  case 1:
                   $__swJSW492__0=
                    $__;
                   break;}
                $__swJSW491__0=
                 $__swJSW492__0;
                break;}
             $__swJSW490__0=
              $__swJSW491__0;
             break;
            case 1:
             $__swJSW490__0=
              $__;
             break;}
          return $__swJSW490__0;});
$UHC.$Base.$__76__33677__0NEW5011UNQ8021CCN=
 new _F_(function($__,$s,$__3)
         {var $__4=
           new _A_($UHC.$Base.$isSpace,[$__3]);
          var $__5=
           _e_($__4);
          var $__swJSW494__0;
          switch($__5._tag_)
           {case 0:
             $__swJSW494__0=
              $__;
             break;
            case 1:
             var $__6=
              new _A_($UHC.$Base.$dropWhile,[$UHC.$Base.$isSpace,$s]);
             var $__7=
              new _A_($UHC.$Base.$_3a,[$__6,$UHC.$Base.$_5b_5d]);
             $__swJSW494__0=
              new _A_($UHC.$Base.$concatMap,[$UHC.$Base.$_24okUNQ8027,$__7]);
             break;}
          return $__swJSW494__0;});
$UHC.$Base.$_24okUNQ8027=
 new _F_(function($_24x)
         {var $__=
           _e_($_24x);
          var $__swJSW495__0;
          switch($__._tag_)
           {case 0:
             var $__5=
              _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,92,$__._1]));
             var $__swJSW496__0;
             switch($__5._tag_)
              {case 0:
                $__swJSW496__0=
                 $UHC.$Base.$_5b_5d;
                break;
               case 1:
                var $__6=
                 new _A_($UHC.$Base.$packedStringToString,[""]);
                var $__7=
                 [$__6,$__._2];
                var $__8=
                 new _A_($UHC.$Base.$_3a,[$__7,$UHC.$Base.$_5b_5d]);
                $__swJSW496__0=
                 $__8;
                break;}
             $__swJSW495__0=
              $__swJSW496__0;
             break;
            case 1:
             $__swJSW495__0=
              $UHC.$Base.$_5b_5d;
             break;}
          return $__swJSW495__0;});
$UHC.$Base.$lexStringUNQ8005=
 new _F_(function($x1)
         {var $__=
           new _A_($UHC.$Base.$__76__33928__0NEW5030UNQ8045CCN,[$x1]);
          var $__3=
           _e_($x1);
          var $__swJSW497__0;
          switch($__3._tag_)
           {case 0:
             var $__6=
              _e_(new _A_($UHC.$Base.$_3d_3d,[$UHC.$Base.$Eq__DCT74__56__0,34,$__3._1]));
             var $__swJSW498__0;
             switch($__6._tag_)
              {case 0:
                $__swJSW498__0=
                 $__;
                break;
               case 1:
                var $__7=
                 new _A_($UHC.$Base.$packedStringToString,["\""]);
                var $__8=
                 [$__7,$__3._2];
                var $__9=
                 new _A_($UHC.$Base.$_3a,[$__8,$UHC.$Base.$_5b_5d]);
                $__swJSW498__0=
                 $__9;
                break;}
             $__swJSW497__0=
              $__swJSW498__0;
             break;
            case 1:
             $__swJSW497__0=
              $__;
             break;}
          return $__swJSW497__0;});
$UHC.$Base.$__76__33928__0NEW5030UNQ8045CCN=
 new _F_(function($x1)
         {var $__=
           new _A_($UHC.$Base.$lexStrItemUNQ8003,[$x1]);
          return new _A_($UHC.$Base.$concatMap,[$UHC.$Base.$_24okUNQ8047,$__]);});
$UHC.$Base.$_24okUNQ8047=
 new _F_(function($_24x)
         {var $__=
           _e_($_24x);
          var $__5=
           new _A_($UHC.$Base.$lexStringUNQ8005,[$__[1]]);
          var $__6=
           new _A_($UHC.$Base.$_24okUNQ8064,[$__[0]]);
          return new _A_($UHC.$Base.$concatMap,[$__6,$__5]);});
$UHC.$Base.$_24okUNQ8064=
 new _F_(function($ch,$_24x)
         {var $__=
           _e_($_24x);
          var $__6=
           new _A_($UHC.$Base.$_2b_2b,[$ch,$__[0]]);
          var $__7=
           [$__6,$__[1]];
          var $__8=
           new _A_($UHC.$Base.$_3a,[$__7,$UHC.$Base.$_5b_5d]);
          return $__8;});
$UHC.$Base.$lex=
 new _F_(function($x1)
         {var $__=
           _e_($x1);
          var $__swJSW501__0;
          switch($__._tag_)
           {case 0:
             var $c5=
              new _A_($UHC.$Base.$cNEW4871UNQ7768CCN,[$__._2,$__._1]);
             var $__6=
              new _A_($UHC.$Base.$isSpace,[$__._1]);
             var $__7=
              _e_($__6);
             var $__swJSW502__0;
             switch($__7._tag_)
              {case 0:
                $__swJSW502__0=
                 $c5;
                break;
               case 1:
                var $__8=
                 new _A_($UHC.$Base.$dropWhile,[$UHC.$Base.$isSpace,$__._2]);
                var $__9=
                 new _A_($UHC.$Base.$lex,[$__8]);
                $__swJSW502__0=
                 $__9;
                break;}
             $__swJSW501__0=
              $__swJSW502__0;
             break;
            case 1:
             var $__10=
              new _A_($UHC.$Base.$packedStringToString,[""]);
             var $__11=
              new _A_($UHC.$Base.$packedStringToString,[""]);
             var $__12=
              [$__11,$__10];
             var $__13=
              new _A_($UHC.$Base.$_3a,[$__12,$UHC.$Base.$_5b_5d]);
             $__swJSW501__0=
              $__13;
             break;}
          return $__swJSW501__0;});
$UHC.$Base.$optionalUNQ8106=
 new _F_(function($g,$r)
         {var $__=
           new _A_($UHC.$Base.$mandatoryUNQ8107,[$g,$r]);
          var $__4=
           new _A_($g,[$r]);
          return new _A_($UHC.$Base.$_2b_2b,[$__4,$__]);});
$UHC.$Base.$mandatoryUNQ8107=
 new _F_(function($g,$r)
         {var $__=
           new _A_($UHC.$Base.$lex,[$r]);
          var $__4=
           new _A_($UHC.$Base.$_24okUNQ8111,[$g]);
          return new _A_($UHC.$Base.$concatMap,[$__4,$__]);});
$UHC.$Base.$readParen=
 new _F_(function($b,$g)
         {var $__=
           _e_($b);
          var $__swJSW503__0;
          switch($__._tag_)
           {case 0:
             var $__4=
              new _A_($UHC.$Base.$optionalUNQ8106,[$g]);
             $__swJSW503__0=
              $__4;
             break;
            case 1:
             var $__5=
              new _A_($UHC.$Base.$mandatoryUNQ8107,[$g]);
             $__swJSW503__0=
              $__5;
             break;}
          return $__swJSW503__0;});
$UHC.$Base.$Read__NEW5112CLS74__41__0DFLUHC_2eBase_2ereadList=
 new _F_(function($Read__)
         {var $__=
           new _A_($UHC.$Base.$__78__10227__0,[$Read__]);
          return new _A_($UHC.$Base.$readParen,[$UHC.$Base.$False__,$__]);});
$UHC.$Base.$Read__CLS74__41__0=
 new _F_(function($Read__)
         {var $Read__CLS74__41__0DFLUHC_2eBase_2ereadList=
           new _A_($UHC.$Base.$Read__NEW5112CLS74__41__0DFLUHC_2eBase_2ereadList,[$Read__]);
          var $Read__2=
           {_tag_:0,_1:$Read__CLS74__41__0DFLUHC_2eBase_2ereadList,_2:$UHC.$Base.$undefined};
          return $Read__2;});
$UHC.$Base.$__74__51__0NEW5216UNQ9532EVLRDC=
 new _F_(function($__)
         {var $Read__=
           _e_(new _A_($UHC.$Base.$Read__CLS74__41__0,[$__]));
          var $__5=
           {_tag_:0,_1:$Read__._1,_2:$UHC.$Base.$__74__51__0DFLUHC_2eBase_2ereadsPrec};
          return $__5;});
$UHC.$Base.$__74__51__0NEW5214UNQ9531RDC=
 new _F_(function($__)
         {var $__2=
           new _A_($UHC.$Base.$__74__51__0NEW5216UNQ9532EVLRDC,[$__]);
          return $__2;});
$UHC.$Base.$__74__51__0UNQ9531RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$__74__51__0NEW5214UNQ9531RDC,[$UHC.$Base.$__74__51__0UNQ9531RDC]);}),[]);
$UHC.$Base.$__74__51__0=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$__74__51__0UNQ9531RDC;}),[]);
$UHC.$Base.$flip=
 new _F_(function($f,$x,$y)
         {return new _A_($f,[$y,$x]);});
$Language.$UHC.$JS.$JQuery.$JQuery.$__toggleClass=
 new _F_(function($__,$__2,$__3)
         {var $__4=
           _e_($__);
          var $__5=
           _e_($__2);
          var $__6=
           _e_($__4.toggleClass($__5));
          var $__7=
           _e_([]);
          return [$__3,$__7];});
$Language.$UHC.$JS.$JQuery.$JQuery.$toggleClass=
 new _F_(function($jq)
         {var $__=
           new _A_($Language.$UHC.$JS.$Types.$toJS,[$Language.$UHC.$JS.$ECMA.$String.$ToJS__DCT40__2__0]);
          var $__3=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$__toggleClass,[$jq]);
          return new _A_($UHC.$Base.$_2e,[$__3,$__]);});
$Language.$UHC.$JS.$JQuery.$JQuery.$toggleClassString=
 new _F_(function($sel,$c)
         {var $__=
           new _A_($UHC.$Base.$flip,[$Language.$UHC.$JS.$JQuery.$JQuery.$toggleClass,$c]);
          var $__4=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$jQuery,[$sel]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__4,$__]);});
$UHC.$Base.$maybe=
 new _F_(function($x1,$x2,$x3)
         {var $x34=
           _e_($x3);
          var $__swJSW505__0;
          switch($x34._tag_)
           {case 0:
             var $__=
              new _A_($x2,[$x34._1]);
             $__swJSW505__0=
              $__;
             break;
            case 1:
             $__swJSW505__0=
              $x1;
             break;}
          return $__swJSW505__0;});
$UHC.$Base.$Just__=
 new _F_(function($x1)
         {return {_tag_:0,_1:$x1};});
$UHC.$Base.$Nothing__=
 new _A_(new _F_(function()
                 {return {_tag_:1};}),[]);
$UHC.$Base.$otherwise=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$True__;}),[]);
$Data.$Map.$__30__292__0NEW2UNQ28CCN=
 new _F_(function($__,$x1,$x2)
         {var $x24=
           _e_($x2);
          var $__swJSW506__0;
          switch($x24._tag_)
           {case 0:
             var $__7=
              _e_($x24._1);
             var $__10=
              new _A_($UHC.$Base.$_3d_3d,[$__,$x1,$__7[0]]);
             var $__11=
              _e_($__10);
             var $__swJSW508__0;
             switch($__11._tag_)
              {case 0:
                var $__12=
                 _e_($UHC.$Base.$otherwise);
                var $__swJSW509__0;
                switch($__12._tag_)
                 {case 0:
                   $__swJSW509__0=
                    $UHC.$Base.$undefined;
                   break;
                  case 1:
                   var $__13=
                    new _A_($Data.$Map.$lookup,[$__,$x1,$x24._2]);
                   $__swJSW509__0=
                    $__13;
                   break;}
                $__swJSW508__0=
                 $__swJSW509__0;
                break;
               case 1:
                var $__14=
                 new _A_($UHC.$Base.$Just__,[$__7[1]]);
                $__swJSW508__0=
                 $__14;
                break;}
             $__swJSW506__0=
              $__swJSW508__0;
             break;
            case 1:
             $__swJSW506__0=
              $UHC.$Base.$undefined;
             break;}
          return $__swJSW506__0;});
$Data.$Map.$lookup=
 new _F_(function($__,$x1,$x2)
         {var $__4=
           new _A_($Data.$Map.$__30__292__0NEW2UNQ28CCN,[$__,$x1,$x2]);
          var $x25=
           _e_($x2);
          var $__swJSW510__0;
          switch($x25._tag_)
           {case 0:
             $__swJSW510__0=
              $__4;
             break;
            case 1:
             $__swJSW510__0=
              $UHC.$Base.$Nothing__;
             break;}
          return $__swJSW510__0;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__=
 new _F_(function($x1,$x2)
         {return {_tag_:0,_1:$x1,_2:$x2};});
$Language.$Prolog.$NanoProlog.$NanoProlog.$Var__=
 new _F_(function($x1)
         {return {_tag_:1,_1:$x1};});
$UHC.$Base.$primEqChar=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_($__2);
          return primEqInt($__3,$__4);});
$UHC.$Base.$Eq__NEW1755UNQ10102EVLDCT74__56__0RDC=
 new _F_(function($Eq__)
         {var $Eq__2=
           _e_(new _A_($UHC.$Base.$Eq__CLS74__4__0,[$Eq__]));
          var $__5=
           {_tag_:0,_1:$Eq__2._1,_2:$UHC.$Base.$primEqChar};
          return $__5;});
$UHC.$Base.$Eq__NEW1753UNQ10101DCT74__56__0RDC=
 new _F_(function($Eq__)
         {var $Eq__2=
           new _A_($UHC.$Base.$Eq__NEW1755UNQ10102EVLDCT74__56__0RDC,[$Eq__]);
          return $Eq__2;});
$UHC.$Base.$Eq__UNQ10101DCT74__56__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Eq__NEW1753UNQ10101DCT74__56__0RDC,[$UHC.$Base.$Eq__UNQ10101DCT74__56__0RDC]);}),[]);
$UHC.$Base.$Eq__DCT74__56__0=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$Eq__UNQ10101DCT74__56__0RDC;}),[]);
$UHC.$Base.$__Rep0_5b_5dDFLUHC_2eBase_2eto0GENRepresentable0=
 new _F_(function($proj__1)
         {var $proj__2=
           _e_($proj__1);
          var $__swJSW512__0;
          switch($proj__2._tag_)
           {case 0:
             var $proj__4=
              _e_($proj__2.unL1);
             $__swJSW512__0=
              $UHC.$Base.$_5b_5d;
             break;
            case 1:
             var $proj__6=
              _e_($proj__2.unR1);
             var $__=
              new _A_($UHC.$Base.$_3a,[$proj__6._1,$proj__6._2]);
             $__swJSW512__0=
              $__;
             break;}
          return $__swJSW512__0;});
$UHC.$Base.$K1__=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$id;}),[]);
$UHC.$Base.$R1__=
 new _F_(function($x1)
         {return {_tag_:1,unR1:$x1};});
$UHC.$Base.$M1__=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$id;}),[]);
$UHC.$Base.$L1__=
 new _F_(function($x1)
         {return {_tag_:0,unL1:$x1};});
$UHC.$Base.$U1__=
 new _A_(new _F_(function()
                 {return {_tag_:0};}),[]);
$UHC.$Base.$_3a_2a_3a=
 new _F_(function($x1,$x2)
         {return {_tag_:0,_1:$x1,_2:$x2};});
$UHC.$Base.$__Rep0_5b_5dDFLUHC_2eBase_2efrom0GENRepresentable0=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          var $__swJSW515__0;
          switch($x2._tag_)
           {case 0:
             var $__5=
              new _A_($UHC.$Base.$K1__,[$x2._2]);
             var $__6=
              new _A_($UHC.$Base.$M1__,[$__5]);
             var $__7=
              new _A_($UHC.$Base.$K1__,[$x2._1]);
             var $__8=
              new _A_($UHC.$Base.$M1__,[$__7]);
             var $__9=
              new _A_($UHC.$Base.$_3a_2a_3a,[$__8,$__6]);
             var $__10=
              new _A_($UHC.$Base.$M1__,[$__9]);
             var $__11=
              new _A_($UHC.$Base.$R1__,[$__10]);
             var $__12=
              new _A_($UHC.$Base.$M1__,[$__11]);
             $__swJSW515__0=
              $__12;
             break;
            case 1:
             var $__=
              new _A_($UHC.$Base.$M1__,[$UHC.$Base.$U1__]);
             var $__14=
              new _A_($UHC.$Base.$L1__,[$__]);
             var $__15=
              new _A_($UHC.$Base.$M1__,[$__14]);
             $__swJSW515__0=
              $__15;
             break;}
          return $__swJSW515__0;});
$UHC.$Base.$Representable0__CLS74__369__0=
 new _F_(function($Representable0__)
         {var $Representable0__2=
           {_tag_:0,_1:$UHC.$Base.$undefined,_2:$UHC.$Base.$undefined};
          return $Representable0__2;});
$UHC.$Base.$__Rep0_5b_5dNEW1144UNQ1262EVLSDCGENRepresentable0=
 new _F_(function($__)
         {var $Representable0__=
           _e_(new _A_($UHC.$Base.$Representable0__CLS74__369__0,[$__]));
          var $__5=
           {_tag_:0,_1:$UHC.$Base.$__Rep0_5b_5dDFLUHC_2eBase_2efrom0GENRepresentable0,_2:$UHC.$Base.$__Rep0_5b_5dDFLUHC_2eBase_2eto0GENRepresentable0};
          return $__5;});
$UHC.$Base.$__Rep0_5b_5dNEW1142UNQ1261SDCGENRepresentable0=
 new _F_(function($__)
         {var $__2=
           new _A_($UHC.$Base.$__Rep0_5b_5dNEW1144UNQ1262EVLSDCGENRepresentable0,[$__]);
          return $__2;});
$UHC.$Base.$__Rep0_5b_5dUNQ1261SDCGENRepresentable0=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$__Rep0_5b_5dNEW1142UNQ1261SDCGENRepresentable0,[$UHC.$Base.$__Rep0_5b_5dUNQ1261SDCGENRepresentable0]);}),[]);
$UHC.$Base.$__Rep0_5b_5dGENRepresentable0=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$__Rep0_5b_5dUNQ1261SDCGENRepresentable0;}),[]);
$UHC.$Base.$_2f_3d=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._1;});
$UHC.$Base.$Eq__CLS74__4__0DFLUHC_2eBase_2e_3d_3d=
 new _F_(function($Eq__,$x,$y)
         {var $__=
           new _A_($UHC.$Base.$_2f_3d,[$Eq__,$x,$y]);
          return new _A_($UHC.$Base.$not,[$__]);});
$UHC.$Base.$not=
 new _F_(function($x1)
         {var $__=
           _e_($x1);
          var $__swJSW518__0;
          switch($__._tag_)
           {case 0:
             $__swJSW518__0=
              $UHC.$Base.$True__;
             break;
            case 1:
             $__swJSW518__0=
              $UHC.$Base.$False__;
             break;}
          return $__swJSW518__0;});
$UHC.$Base.$Eq__CLS74__4__0DFLUHC_2eBase_2e_2f_3d=
 new _F_(function($Eq__,$x,$y)
         {var $__=
           new _A_($UHC.$Base.$_3d_3d,[$Eq__,$x,$y]);
          return new _A_($UHC.$Base.$not,[$__]);});
$UHC.$Base.$Eq__CLS74__4__0=
 new _F_(function($Eq__)
         {var $__=
           new _A_($UHC.$Base.$Eq__CLS74__4__0DFLUHC_2eBase_2e_3d_3d,[$Eq__]);
          var $__3=
           new _A_($UHC.$Base.$Eq__CLS74__4__0DFLUHC_2eBase_2e_2f_3d,[$Eq__]);
          var $Eq__4=
           {_tag_:0,_1:$__3,_2:$__};
          return $Eq__4;});
$UHC.$Base.$Eq__NEW1960UNQ10082EVLDCT74__394__0RDC=
 new _F_(function($Eq__,$Eq__2)
         {var $Eq__3=
           _e_(new _A_($UHC.$Base.$Eq__CLS74__4__0,[$Eq__]));
          var $__6=
           {_tag_:0,_1:$Eq__3._1,_2:$Eq__2};
          return $__6;});
$UHC.$Base.$Eq__NEW1949UNQ10070DCT74__394__0RDC=
 new _F_(function($Eq__,$__,$__3,$__4,$__5,$__6,$__7,$__8,$Eq__9,$__10)
         {var $Eq__11=
           new _A_($UHC.$Base.$Eq__NEW1960UNQ10082EVLDCT74__394__0RDC,[$Eq__,$Eq__9]);
          return $Eq__11;});
$UHC.$Base.$_3d_3d=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._2;});
$UHC.$Base.$Eq_27__DCT74__390__0DFLUHC_2eBase_2egeq_27=
 new _F_(function($__,$__2,$__3)
         {return new _A_($UHC.$Base.$_3d_3d,[$__,$__2,$__3]);});
$UHC.$Base.$Eq_27__NEW1652UNQ10212EVLDCT74__390__0RDC=
 new _F_(function($Eq_27__,$__)
         {var $Eq_27__3=
           _e_(new _A_($UHC.$Base.$Eq_27__CLS74__388__0,[$Eq_27__]));
          var $__5=
           new _A_($UHC.$Base.$Eq_27__DCT74__390__0DFLUHC_2eBase_2egeq_27,[$__]);
          var $__6=
           {_tag_:0,_1:$__5};
          return $__6;});
$UHC.$Base.$Eq_27__NEW1649UNQ10210DCT74__390__0RDC=
 new _F_(function($Eq_27__,$__)
         {var $Eq_27__3=
           new _A_($UHC.$Base.$Eq_27__NEW1652UNQ10212EVLDCT74__390__0RDC,[$Eq_27__,$__]);
          return $Eq_27__3;});
$UHC.$Base.$Eq_27__DCT74__390__0=
 new _F_(function($__)
         {var $Eq_27__=
           _i_();
          _i_set_($Eq_27__,new _A_($UHC.$Base.$Eq_27__NEW1649UNQ10210DCT74__390__0RDC,[$Eq_27__,$__]));
          return $Eq_27__;});
$UHC.$Base.$_26_26=
 new _F_(function($x1,$x2)
         {var $x13=
           _e_($x1);
          var $__swJSW522__0;
          switch($x13._tag_)
           {case 0:
             $__swJSW522__0=
              $UHC.$Base.$False__;
             break;
            case 1:
             $__swJSW522__0=
              $x2;
             break;}
          return $__swJSW522__0;});
$UHC.$Base.$__78__4183__0=
 new _F_(function($__,$__2,$a1,$b1,$__5)
         {var $__6=
           _e_($__5);
          var $__9=
           new _A_($UHC.$Base.$geq_27,[$__2,$b1,$__6._2]);
          var $__10=
           new _A_($UHC.$Base.$geq_27,[$__,$a1,$__6._1]);
          var $__11=
           new _A_($UHC.$Base.$_26_26,[$__10,$__9]);
          return $__11;});
$UHC.$Base.$Eq_27__DCT74__393__0DFLUHC_2eBase_2egeq_27=
 new _F_(function($__,$__2,$__3)
         {var $__4=
           _e_($__3);
          return new _A_($UHC.$Base.$__78__4183__0,[$__,$__2,$__4._1,$__4._2]);});
$UHC.$Base.$Eq_27__NEW1939UNQ10194EVLDCT74__393__0RDC=
 new _F_(function($__,$__2,$Eq_27__)
         {var $Eq_27__4=
           _e_(new _A_($UHC.$Base.$Eq_27__CLS74__388__0,[$Eq_27__]));
          var $__6=
           new _A_($UHC.$Base.$Eq_27__DCT74__393__0DFLUHC_2eBase_2egeq_27,[$__,$__2]);
          var $__7=
           {_tag_:0,_1:$__6};
          return $__7;});
$UHC.$Base.$Eq_27__NEW1935UNQ10191DCT74__393__0RDC=
 new _F_(function($__,$__2,$Eq_27__)
         {var $Eq_27__4=
           new _A_($UHC.$Base.$Eq_27__NEW1939UNQ10194EVLDCT74__393__0RDC,[$__,$__2,$Eq_27__]);
          return $Eq_27__4;});
$UHC.$Base.$Eq_27__DCT74__393__0=
 new _F_(function($__,$__2)
         {var $Eq_27__=
           _i_();
          _i_set_($Eq_27__,new _A_($UHC.$Base.$Eq_27__NEW1935UNQ10191DCT74__393__0RDC,[$__,$__2,$Eq_27__]));
          return $Eq_27__;});
$UHC.$Base.$False__=
 new _A_(new _F_(function()
                 {return {_tag_:0};}),[]);
$UHC.$Base.$Eq_27__DCT74__392__0DFLUHC_2eBase_2egeq_27=
 new _F_(function($__,$__2,$x1,$x2)
         {var $x15=
           _e_($x1);
          var $__swJSW526__0;
          switch($x15._tag_)
           {case 0:
             var $x27=
              _e_($x2);
             var $__swJSW527__0;
             switch($x27._tag_)
              {case 0:
                var $__9=
                 new _A_($UHC.$Base.$geq_27,[$__,$x15.unL1,$x27.unL1]);
                $__swJSW527__0=
                 $__9;
                break;
               case 1:
                $__swJSW527__0=
                 $UHC.$Base.$False__;
                break;}
             $__swJSW526__0=
              $__swJSW527__0;
             break;
            case 1:
             var $x212=
              _e_($x2);
             var $__swJSW528__0;
             switch($x212._tag_)
              {case 0:
                $__swJSW528__0=
                 $UHC.$Base.$False__;
                break;
               case 1:
                var $__15=
                 new _A_($UHC.$Base.$geq_27,[$__2,$x15.unR1,$x212.unR1]);
                $__swJSW528__0=
                 $__15;
                break;}
             $__swJSW526__0=
              $__swJSW528__0;
             break;}
          return $__swJSW526__0;});
$UHC.$Base.$Eq_27__NEW1846UNQ10159EVLDCT74__392__0RDC=
 new _F_(function($__,$Eq_27__,$__3)
         {var $Eq_27__4=
           _e_(new _A_($UHC.$Base.$Eq_27__CLS74__388__0,[$Eq_27__]));
          var $__6=
           new _A_($UHC.$Base.$Eq_27__DCT74__392__0DFLUHC_2eBase_2egeq_27,[$__,$__3]);
          var $__7=
           {_tag_:0,_1:$__6};
          return $__7;});
$UHC.$Base.$Eq_27__NEW1842UNQ10156DCT74__392__0RDC=
 new _F_(function($__,$Eq_27__,$__3)
         {var $Eq_27__4=
           new _A_($UHC.$Base.$Eq_27__NEW1846UNQ10159EVLDCT74__392__0RDC,[$__,$Eq_27__,$__3]);
          return $Eq_27__4;});
$UHC.$Base.$Eq_27__DCT74__392__0=
 new _F_(function($__,$__2)
         {var $Eq_27__=
           _i_();
          _i_set_($Eq_27__,new _A_($UHC.$Base.$Eq_27__NEW1842UNQ10156DCT74__392__0RDC,[$__,$Eq_27__,$__2]));
          return $Eq_27__;});
$UHC.$Base.$True__=
 new _A_(new _F_(function()
                 {return {_tag_:1};}),[]);
$UHC.$Base.$Eq_27__DCT74__389__0DFLUHC_2eBase_2egeq_27=
 new _F_(function($__,$__2)
         {return $UHC.$Base.$True__;});
$UHC.$Base.$Eq_27__NEW555UNQ10149EVLDCT74__389__0RDC=
 new _F_(function($Eq_27__)
         {var $Eq_27__2=
           _e_(new _A_($UHC.$Base.$Eq_27__CLS74__388__0,[$Eq_27__]));
          var $__4=
           {_tag_:0,_1:$UHC.$Base.$Eq_27__DCT74__389__0DFLUHC_2eBase_2egeq_27};
          return $__4;});
$UHC.$Base.$Eq_27__NEW553UNQ10148DCT74__389__0RDC=
 new _F_(function($Eq_27__)
         {var $Eq_27__2=
           new _A_($UHC.$Base.$Eq_27__NEW555UNQ10149EVLDCT74__389__0RDC,[$Eq_27__]);
          return $Eq_27__2;});
$UHC.$Base.$Eq_27__UNQ10148DCT74__389__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Eq_27__NEW553UNQ10148DCT74__389__0RDC,[$UHC.$Base.$Eq_27__UNQ10148DCT74__389__0RDC]);}),[]);
$UHC.$Base.$Eq_27__DCT74__389__0=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$Eq_27__UNQ10148DCT74__389__0RDC;}),[]);
$UHC.$Base.$Eq_27__DCT74__391__0DFLUHC_2eBase_2egeq_27=
 new _F_(function($__,$__2,$__3)
         {return new _A_($UHC.$Base.$geq_27,[$__,$__2,$__3]);});
$UHC.$Base.$Eq_27__CLS74__388__0=
 new _F_(function($Eq_27__)
         {var $Eq_27__2=
           {_tag_:0,_1:$UHC.$Base.$undefined};
          return $Eq_27__2;});
$UHC.$Base.$Eq_27__NEW1830UNQ10137EVLDCT74__391__0RDC=
 new _F_(function($Eq_27__,$__)
         {var $Eq_27__3=
           _e_(new _A_($UHC.$Base.$Eq_27__CLS74__388__0,[$Eq_27__]));
          var $__5=
           new _A_($UHC.$Base.$Eq_27__DCT74__391__0DFLUHC_2eBase_2egeq_27,[$__]);
          var $__6=
           {_tag_:0,_1:$__5};
          return $__6;});
$UHC.$Base.$Eq_27__NEW1827UNQ10135DCT74__391__0RDC=
 new _F_(function($Eq_27__,$__)
         {var $Eq_27__3=
           new _A_($UHC.$Base.$Eq_27__NEW1830UNQ10137EVLDCT74__391__0RDC,[$Eq_27__,$__]);
          return $Eq_27__3;});
$UHC.$Base.$Eq_27__DCT74__391__0=
 new _F_(function($__)
         {var $Eq_27__=
           _i_();
          _i_set_($Eq_27__,new _A_($UHC.$Base.$Eq_27__NEW1827UNQ10135DCT74__391__0RDC,[$Eq_27__,$__]));
          return $Eq_27__;});
$UHC.$Base.$geq_27=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._1;});
$UHC.$Base.$from0=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._1;});
$UHC.$Base.$geqdefault=
 new _F_(function($__,$__2,$rep,$x,$y)
         {var $__6=
           new _A_($UHC.$Base.$from0,[$__,$y]);
          var $__7=
           new _A_($UHC.$Base.$from0,[$__,$x]);
          return new _A_($UHC.$Base.$geq_27,[$__2,$__7,$__6]);});
$UHC.$Base.$Eq__DCT74__394__0=
 new _F_(function($__)
         {var $__2=
           new _A_($UHC.$Base.$Eq_27__DCT74__391__0,[$UHC.$Base.$Eq_27__DCT74__389__0]);
          var $__3=
           new _A_($UHC.$Base.$Eq_27__DCT74__390__0,[$__]);
          var $__4=
           new _A_($UHC.$Base.$Eq_27__DCT74__391__0,[$__3]);
          var $Eq__=
           _i_();
          var $__6=
           _i_();
          var $__7=
           _i_();
          var $__8=
           _i_();
          var $__9=
           _i_();
          var $__10=
           _i_();
          var $Eq__DCT74__394__0DFLUHC_2eBase_2e_3d_3d=
           _i_();
          var $__11=
           _i_();
          _i_set_($Eq__,new _A_($UHC.$Base.$Eq__NEW1949UNQ10070DCT74__394__0RDC,[$Eq__,$__6,$__4,$__8,$__9,$__2,$__10,$__7,$Eq__DCT74__394__0DFLUHC_2eBase_2e_3d_3d,$__11]));
          _i_set_($__6,new _A_($UHC.$Base.$Eq_27__DCT74__391__0,[$__7]));
          _i_set_($__7,new _A_($UHC.$Base.$Eq_27__DCT74__390__0,[$Eq__]));
          _i_set_($__8,new _A_($UHC.$Base.$Eq_27__DCT74__393__0,[$__4,$__6]));
          _i_set_($__9,new _A_($UHC.$Base.$Eq_27__DCT74__391__0,[$__8]));
          _i_set_($__10,new _A_($UHC.$Base.$Eq_27__DCT74__392__0,[$__2,$__9]));
          _i_set_($Eq__DCT74__394__0DFLUHC_2eBase_2e_3d_3d,new _A_($UHC.$Base.$geqdefault,[$UHC.$Base.$__Rep0_5b_5dGENRepresentable0,$__11,$UHC.$Base.$undefined]));
          _i_set_($__11,new _A_($UHC.$Base.$Eq_27__DCT74__391__0,[$__10]));
          return $Eq__;});
$UHC.$Base.$id=
 new _F_(function($x)
         {return $x;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$fromEnv=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$id;}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$Subst__NEW473UNQ850DCT52__10__0RDC=
 new _F_(function($Subst__,$__)
         {var $Subst__3=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Subst__NEW476UNQ854EVLDCT52__10__0RDC,[$Subst__,$__]);
          return $Subst__3;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$Subst__NEW476UNQ854EVLDCT52__10__0RDC=
 new _F_(function($Subst__,$__)
         {var $Subst__3=
           _e_(new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Subst__CLS52__8__0,[$Subst__]));
          var $__5=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Subst__DCT52__10__0DFLLanguage_2eProlog_2eNanoProlog_2eNanoProlog_2esubst,[$__]);
          var $__6=
           {_tag_:0,_1:$__5};
          return $__6;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$Subst__DCT52__10__0DFLLanguage_2eProlog_2eNanoProlog_2eNanoProlog_2esubst=
 new _F_(function($__,$x1,$x2)
         {var $x24=
           _e_($x2);
          var $__swJSW535__0;
          switch($x24._tag_)
           {case 0:
             var $__7=
              new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$subst,[$__,$x1,$x24._2]);
             var $__8=
              new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Fun__,[$x24._1,$__7]);
             $__swJSW535__0=
              $__8;
             break;
            case 1:
             var $__10=
              new _A_($UHC.$Base.$Eq__DCT74__394__0,[$UHC.$Base.$Eq__DCT74__56__0]);
             var $__11=
              new _A_($UHC.$Base.$Eq__DCT74__394__0,[$UHC.$Base.$Eq__DCT74__56__0]);
             var $__12=
              new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$fromEnv,[$x1]);
             var $__13=
              new _A_($Data.$Map.$lookup,[$__11,$x24._1,$__12]);
             var $__14=
              new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Var__,[$x24._1]);
             var $__15=
              new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$subsUNQ882,[$x1,$x24._1,$__10]);
             $__swJSW535__0=
              new _A_($UHC.$Base.$maybe,[$__14,$__15,$__13]);
             break;}
          return $__swJSW535__0;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$subsUNQ882=
 new _F_(function($x1,$x,$__,$x14)
         {var $__5=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$subst,[$Language.$Prolog.$NanoProlog.$NanoProlog.$Subst__DCT52__10__0,$x1,$x14]);
          var $__6=
           _e_($x14);
          var $__swJSW536__0;
          switch($__6._tag_)
           {case 0:
             $__swJSW536__0=
              $__5;
             break;
            case 1:
             var $__10=
              new _A_($UHC.$Base.$_3d_3d,[$__,$x,$__6._1]);
             var $__11=
              _e_($__10);
             var $__swJSW537__0;
             switch($__11._tag_)
              {case 0:
                $__swJSW537__0=
                 $__5;
                break;
               case 1:
                var $__12=
                 new _A_($UHC.$Base.$packedStringToString,["Occurs check in Subst.Term"]);
                var $__13=
                 new _A_($UHC.$Base.$error,[$__12]);
                $__swJSW537__0=
                 $__13;
                break;}
             $__swJSW536__0=
              $__swJSW537__0;
             break;}
          return $__swJSW536__0;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$Subst__UNQ850DCT52__10__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Subst__NEW473UNQ850DCT52__10__0RDC,[$Language.$Prolog.$NanoProlog.$NanoProlog.$Subst__UNQ850DCT52__10__0RDC,$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__4187__2__0UNQ851]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__4187__2__0UNQ851=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Subst__DCT52__9__0,[$Language.$Prolog.$NanoProlog.$NanoProlog.$Subst__UNQ850DCT52__10__0RDC]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$__54__4127__2__0UNQ852=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Eq__DCT74__394__0,[$UHC.$Base.$Eq__DCT74__56__0]);}),[]);
$Language.$Prolog.$NanoProlog.$NanoProlog.$Subst__DCT52__10__0=
 new _A_(new _F_(function()
                 {return $Language.$Prolog.$NanoProlog.$NanoProlog.$Subst__UNQ850DCT52__10__0RDC;}),[]);
$Prolog.$Subst__DCT28__3__0DFLLanguage_2eProlog_2eNanoProlog_2eNanoProlog_2esubst=
 new _F_(function($__,$env,$__3)
         {var $__4=
           _e_($__3);
          var $__7=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$subst,[$__,$env,$__4.subForest]);
          var $__8=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$subst,[$Language.$Prolog.$NanoProlog.$NanoProlog.$Subst__DCT52__10__0,$env,$__4.rootLabel]);
          var $__9=
           new _A_($Data.$Tree.$Node__,[$__8,$__7]);
          return $__9;});
$Prolog.$Subst__NEW718UNQ383EVLDCT28__3__0RDC=
 new _F_(function($__,$Subst__)
         {var $Subst__3=
           _e_(new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Subst__CLS52__8__0,[$Subst__]));
          var $__5=
           new _A_($Prolog.$Subst__DCT28__3__0DFLLanguage_2eProlog_2eNanoProlog_2eNanoProlog_2esubst,[$__]);
          var $__6=
           {_tag_:0,_1:$__5};
          return $__6;});
$Prolog.$Subst__NEW715UNQ380DCT28__3__0RDC=
 new _F_(function($__,$Subst__)
         {var $Subst__3=
           new _A_($Prolog.$Subst__NEW718UNQ383EVLDCT28__3__0RDC,[$__,$Subst__]);
          return $Subst__3;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$subst=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._1;});
$UHC.$Base.$_24okUNQ3572=
 new _F_(function($f,$_24x)
         {var $__=
           new _A_($f,[$_24x]);
          return new _A_($UHC.$Base.$_3a,[$__,$UHC.$Base.$_5b_5d]);});
$UHC.$Base.$_2b_2b=
 new _F_(function($x1,$x2)
         {var $x13=
           _e_($x1);
          var $__swJSW541__0;
          switch($x13._tag_)
           {case 0:
             var $__=
              new _A_($UHC.$Base.$_2b_2b,[$x13._2,$x2]);
             var $__7=
              new _A_($UHC.$Base.$_3a,[$x13._1,$__]);
             $__swJSW541__0=
              $__7;
             break;
            case 1:
             $__swJSW541__0=
              $x2;
             break;}
          return $__swJSW541__0;});
$UHC.$Base.$concatMap=
 new _F_(function($x1,$x2)
         {var $x23=
           _e_($x2);
          var $__swJSW542__0;
          switch($x23._tag_)
           {case 0:
             var $__=
              new _A_($UHC.$Base.$concatMap,[$x1,$x23._2]);
             var $__7=
              new _A_($x1,[$x23._1]);
             var $__8=
              new _A_($UHC.$Base.$_2b_2b,[$__7,$__]);
             $__swJSW542__0=
              $__8;
             break;
            case 1:
             $__swJSW542__0=
              $UHC.$Base.$_5b_5d;
             break;}
          return $__swJSW542__0;});
$UHC.$Base.$map=
 new _F_(function($f,$xs)
         {var $__=
           new _A_($UHC.$Base.$_24okUNQ3572,[$f]);
          return new _A_($UHC.$Base.$concatMap,[$__,$xs]);});
$Language.$Prolog.$NanoProlog.$NanoProlog.$Subst__DCT52__9__0DFLLanguage_2eProlog_2eNanoProlog_2eNanoProlog_2esubst=
 new _F_(function($__,$e)
         {var $__3=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$subst,[$__,$e]);
          return new _A_($UHC.$Base.$map,[$__3]);});
$Language.$Prolog.$NanoProlog.$NanoProlog.$Subst__CLS52__8__0=
 new _F_(function($Subst__)
         {var $Subst__2=
           {_tag_:0,_1:$UHC.$Base.$undefined};
          return $Subst__2;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$Subst__NEW428UNQ846EVLDCT52__9__0RDC=
 new _F_(function($__,$Subst__)
         {var $Subst__3=
           _e_(new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Subst__CLS52__8__0,[$Subst__]));
          var $__5=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Subst__DCT52__9__0DFLLanguage_2eProlog_2eNanoProlog_2eNanoProlog_2esubst,[$__]);
          var $__6=
           {_tag_:0,_1:$__5};
          return $__6;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$Subst__NEW425UNQ844DCT52__9__0RDC=
 new _F_(function($__,$Subst__)
         {var $Subst__3=
           new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Subst__NEW428UNQ846EVLDCT52__9__0RDC,[$__,$Subst__]);
          return $Subst__3;});
$Language.$Prolog.$NanoProlog.$NanoProlog.$Subst__DCT52__9__0=
 new _F_(function($__)
         {var $Subst__=
           _i_();
          _i_set_($Subst__,new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Subst__NEW425UNQ844DCT52__9__0RDC,[$__,$Subst__]));
          return $Subst__;});
$Prolog.$__30__6718__2__0UNQ381=
 new _A_(new _F_(function()
                 {return new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$Subst__DCT52__9__0,[$Prolog.$Subst__UNQ380DCT28__3__0RDC]);}),[]);
$Prolog.$Subst__UNQ380DCT28__3__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($Prolog.$Subst__NEW715UNQ380DCT28__3__0RDC,[$Prolog.$__30__6718__2__0UNQ381,$Prolog.$Subst__UNQ380DCT28__3__0RDC]);}),[]);
$Prolog.$Subst__DCT28__3__0=
 new _A_(new _F_(function()
                 {return $Prolog.$Subst__UNQ380DCT28__3__0RDC;}),[]);
$Language.$UHC.$JS.$JQuery.$JQuery.$__replaceWith=
 new _F_(function($__,$__2,$__3)
         {var $__4=
           _e_($__);
          var $__5=
           _e_($__2);
          var $__6=
           _e_($__4.replaceWith($__5));
          var $__7=
           _e_([]);
          return [$__3,$__7];});
$Language.$UHC.$JS.$JQuery.$JQuery.$replaceWith=
 new _A_(new _F_(function()
                 {return $Language.$UHC.$JS.$JQuery.$JQuery.$__replaceWith;}),[]);
$Debug.$__consoleLog=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_(console.log($__3));
          var $__5=
           _e_([]);
          return [$__2,$__5];});
$Debug.$__38__30=
 new _A_(new _F_(function()
                 {return new _A_($Language.$UHC.$JS.$Types.$toJS,[$Language.$UHC.$JS.$ECMA.$String.$ToJS__DCT40__2__0]);}),[]);
$Debug.$consoleLog=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_2e,[$Debug.$__consoleLog,$Debug.$__38__30]);}),[]);
$JCU.$fCheckUNQ246=
 new _F_(function($this,$__)
         {var $__3=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$valString,[$this]);
          var $__4=
           new _A_($JCU.$_24okUNQ400,[$this]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__3,$__4]);});
$JCU.$_24okUNQ400=
 new _F_(function($this,$_24x)
         {var $__=
           new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0,$UHC.$Base.$False__]);
          var $__4=
           new _A_($JCU.$__44__291NEW122,[$this,$_24x]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__4,$__]);});
$JCU.$__44__291NEW122=
 new _F_(function($this,$_24x)
         {var $__=
           new _A_($Models.$tryParseTerm,[$_24x]);
          var $__4=
           new _A_($JCU.$markInvalidTerm,[$this]);
          var $__5=
           _e_($__);
          var $__swJSW544__0;
          switch($__5._tag_)
           {case 0:
             var $__7=
              new _A_($Data.$Tree.$Node__,[$__5._1,$UHC.$Base.$_5b_5d]);
             var $__8=
              new _A_($UHC.$Base.$_24,[$JCU.$replaceRuleTree,$__7]);
             $__swJSW544__0=
              $__8;
             break;
            case 1:
             $__swJSW544__0=
              $__4;
             break;}
          return $__swJSW544__0;});
$JCU.$onDropUNQ235=
 new _F_(function($wp,$lvl,$node,$this,$__,$ui)
         {var $__7=
           new _A_($UHC.$Base.$packedStringToString,["input[type='text']:first"]);
          var $__8=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$findSelector,[$this,$__7]);
          var $__9=
           new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__8,$Language.$UHC.$JS.$JQuery.$JQuery.$valString]);
          var $__10=
           new _A_($JCU.$_24okUNQ258,[$wp,$lvl,$ui]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__9,$__10]);});
$JCU.$_24okUNQ258=
 new _F_(function($wp,$lvl,$ui,$_24x)
         {var $__=
           new _A_($UHC.$Base.$packedStringToString,["innerText"]);
          var $__6=
           new _A_($Language.$UHC.$JS.$Primitives.$getAttr,[$__]);
          var $__7=
           new _A_($UHC.$Base.$packedStringToString,["context"]);
          var $__8=
           new _A_($Language.$UHC.$JS.$Primitives.$getAttr,[$__7]);
          var $__9=
           new _A_($UHC.$Base.$packedStringToString,["draggable"]);
          var $__10=
           new _A_($Language.$UHC.$JS.$Primitives.$getAttr,[$__9,$ui]);
          var $__11=
           new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__10,$__8]);
          var $__12=
           new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__11,$__6]);
          var $__13=
           new _A_($JCU.$_24okUNQ265,[$wp,$lvl,$_24x]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__12,$__13]);});
$JCU.$_24okUNQ265=
 new _F_(function($wp,$lvl,$_24x,$_24x4)
         {var $ruleText=
           new _A_($Language.$UHC.$JS.$Types.$fromJS,[$Language.$UHC.$JS.$ECMA.$String.$FromJS__DCT40__4__0,$_24x4]);
          var $__=
           new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0,$UHC.$Base.$True__]);
          var $__7=
           new _A_($JCU.$__44__332NEW136,[$wp,$lvl,$_24x,$ruleText]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__7,$__]);});
$JCU.$__44__332NEW136=
 new _F_(function($wp,$lvl,$_24x,$ruleText)
         {var $__=
           new _A_($UHC.$Base.$null,[$_24x]);
          var $__6=
           _e_($__);
          var $__swJSW545__0;
          switch($__6._tag_)
           {case 0:
             var $__7=
              new _A_($Models.$tryParseRule,[$ruleText]);
             var $__8=
              _e_($__7);
             var $__swJSW546__0;
             switch($__8._tag_)
              {case 0:
                var $__10=
                 new _A_($Prolog.$dropUnify,[$wp,$lvl,$__8._1]);
                var $__11=
                 _e_($__10);
                var $__14=
                 _e_($__11._1);
                var $__swJSW548__0;
                switch($__14._tag_)
                 {case 0:
                   var $__15=
                    new _A_($UHC.$Base.$packedStringToString,["I could not unify this."]);
                   var $__16=
                    new _A_($Util.$showError,[$__15]);
                   $__swJSW548__0=
                    $__16;
                   break;
                  case 1:
                   var $__17=
                    new _A_($JCU.$replaceRuleTree,[$__11._2]);
                   $__swJSW548__0=
                    $__17;
                   break;}
                $__swJSW546__0=
                 $__swJSW548__0;
                break;
               case 1:
                var $__18=
                 new _A_($UHC.$Base.$packedStringToString,["This should not happen. Dropping an invalid rule here."]);
                var $__19=
                 new _A_($Util.$showError,[$__18]);
                $__swJSW546__0=
                 $__19;
                break;}
             $__swJSW545__0=
              $__swJSW546__0;
             break;
            case 1:
             var $__20=
              new _A_($UHC.$Base.$packedStringToString,["There needs to be a term in the text field!"]);
             var $__21=
              new _A_($Util.$showError,[$__20]);
             $__swJSW545__0=
              $__21;
             break;}
          return $__swJSW545__0;});
$JCU.$fUNQ244=
 new _F_(function($__,$__2,$lvl,$wp,$__5)
         {var $__6=
           _e_($__5);
          return new _A_($JCU.$__44__391__0,[$__,$__2,$lvl,$wp,$__6[1],$__6[0]]);});
$JCU.$build_27UNQ243=
 new _F_(function($__,$__2,$lvl,$wp,$__5)
         {var $__6=
           _e_($__5);
          var $n9=
           _e_($__6[0]);
          var $__12=
           _e_($__6[1]);
          return new _A_($JCU.$__44__435__0,[$__,$__2,$lvl,$wp,$n9,$n9.subForest,$n9.rootLabel,$__12.subForest,$__12.rootLabel]);});
$JCU.$__44__391__0=
 new _F_(function($__,$__2,$lvl,$wp,$n,$jq,$__7)
         {var $__8=
           _e_($__7);
          var $__11=
           [$__8[0],$__8[1]];
          var $__12=
           new _A_($UHC.$Base.$_3a,[$n,$UHC.$Base.$_5b_5d]);
          var $__13=
           new _A_($UHC.$Base.$_2b_2b,[$lvl,$__12]);
          var $__14=
           new _A_($JCU.$build_27UNQ243,[$__,$__2,$__13,$wp,$__11,$UHC.$Base.$True__]);
          var $__15=
           new _A_($JCU.$_24okUNQ388,[$n,$jq]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__14,$__15]);});
$JCU.$_24okUNQ388=
 new _F_(function($n,$jq,$_24x)
         {var $__=
           new _A_($UHC.$Base.$_2b,[$UHC.$Base.$Num__DCT74__101__0,$n,1]);
          var $__5=
           [$jq,$__];
          var $__6=
           new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0,$__5]);
          var $__7=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$append,[$jq,$_24x]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__7,$__6]);});
$JCU.$__44__435__0=
 new _F_(function($__,$__2,$lvl,$wp,$n,$chts,$term,$chstat,$status,$disabled)
         {var $__11=
           new _A_($JCU.$__44__453NEW184,[$__,$__2,$lvl,$wp,$n,$chts,$term,$chstat,$status,$disabled]);
          var $__12=
           new _A_($UHC.$Base.$show,[$__2,$wp]);
          var $__13=
           new _A_($UHC.$Base.$packedStringToString,["; "]);
          var $__14=
           new _A_($UHC.$Base.$_2b_2b,[$__13,$__12]);
          var $__15=
           new _A_($UHC.$Base.$show,[$__,$lvl]);
          var $__16=
           new _A_($UHC.$Base.$_2b_2b,[$__15,$__14]);
          var $__17=
           new _A_($UHC.$Base.$packedStringToString,["build' "]);
          var $__18=
           new _A_($UHC.$Base.$_2b_2b,[$__17,$__16]);
          var $__19=
           new _A_($Debug.$consoleLog,[$__18]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__19,$__11]);});
$JCU.$__44__453NEW184=
 new _F_(function($__,$__2,$lvl,$wp,$n,$chts,$term,$chstat,$status,$disabled)
         {var $__11=
           new _A_($UHC.$Base.$packedStringToString,["<li/>"]);
          var $__12=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$jQuery,[$__11]);
          var $__13=
           new _A_($JCU.$_24okUNQ310,[$__,$__2,$lvl,$wp,$n,$chts,$term,$chstat,$status,$disabled]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__12,$__13]);});
$JCU.$_24okUNQ310=
 new _F_(function($__,$__2,$lvl,$wp,$n,$chts,$term,$chstat,$status,$disabled,$_24x)
         {var $__12=
           new _A_($JCU.$__44__475NEW196,[$__,$__2,$lvl,$wp,$n,$chts,$chstat,$_24x]);
          var $__13=
           new _A_($UHC.$Base.$show,[$UHC.$Base.$Show__DCT74__128__0]);
          var $__14=
           new _A_($UHC.$Base.$map,[$__13,$lvl]);
          var $__15=
           new _A_($UHC.$Base.$packedStringToString,["."]);
          var $__16=
           new _A_($Data.$List.$intercalate,[$__15]);
          var $__17=
           new _A_($UHC.$Base.$_24,[$__16,$__14]);
          var $__18=
           new _A_($UHC.$Base.$show,[$Language.$Prolog.$NanoProlog.$NanoProlog.$Show__DCT52__14__0,$term]);
          var $__19=
           new _A_($Templates.$proof__tree__item,[$__18,$__17,$disabled,$status]);
          var $__20=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$appendString,[$_24x]);
          var $__21=
           new _A_($UHC.$Base.$_24,[$__20,$__19]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__21,$__12]);});
$JCU.$__44__475NEW196=
 new _F_(function($__,$__2,$lvl,$wp,$n,$chts,$chstat,$_24x)
         {var $__9=
           new _A_($UHC.$Base.$packedStringToString,[".dropzone"]);
          var $__10=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$findSelector,[$_24x,$__9]);
          var $__11=
           new _A_($JCU.$_24okUNQ317,[$__,$__2,$lvl,$wp,$n,$chts,$chstat,$_24x]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__10,$__11]);});
$JCU.$_24okUNQ317=
 new _F_(function($__,$__2,$lvl,$wp,$n,$chts,$chstat,$_24x,$_24x9)
         {var $__10=
           new _A_($JCU.$onDropUNQ235,[$wp,$lvl,$n]);
          var $__11=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$mkJUIThisEventHandler,[$__10]);
          var $__12=
           new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__11,$Language.$UHC.$JS.$JQuery.$JQuery.$wrappedJQueryUIEvent]);
          var $__13=
           new _A_($JCU.$_24okUNQ325,[$__,$__2,$lvl,$wp,$chts,$chstat,$_24x,$_24x9]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__12,$__13]);});
$JCU.$_24okUNQ325=
 new _F_(function($__,$__2,$lvl,$wp,$chts,$chstat,$_24x,$_24x8,$_24x9)
         {var $__10=
           new _A_($JCU.$__44__492NEW207,[$__,$__2,$lvl,$wp,$chts,$chstat,$_24x]);
          var $__11=
           new _A_($UHC.$Base.$packedStringToString,["dropHover"]);
          var $__12=
           new _A_($Language.$UHC.$JS.$Types.$toJS,[$Language.$UHC.$JS.$ECMA.$String.$ToJS__DCT40__2__0,$__11]);
          var $__13=
           new _A_($Language.$UHC.$JS.$JQuery.$Droppable.$Droppable__,[$__12,$_24x9]);
          var $__14=
           new _A_($Language.$UHC.$JS.$JQuery.$Droppable.$droppable,[$_24x8]);
          var $__15=
           new _A_($UHC.$Base.$_24,[$__14,$__13]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__15,$__10]);});
$JCU.$__44__492NEW207=
 new _F_(function($__,$__2,$lvl,$wp,$chts,$chstat,$_24x)
         {var $__8=
           new _A_($UHC.$Base.$packedStringToString,["<ul/>"]);
          var $__9=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$jQuery,[$__8]);
          var $__10=
           new _A_($JCU.$_24okUNQ333,[$__,$__2,$lvl,$wp,$chts,$chstat,$_24x]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__9,$__10]);});
$JCU.$_24okUNQ333=
 new _F_(function($__,$__2,$lvl,$wp,$chts,$chstat,$_24x,$_24x8)
         {var $__9=
           new _A_($UHC.$Base.$zip,[$chts,$chstat]);
          var $__10=
           [$_24x8,1];
          var $__11=
           new _A_($JCU.$fUNQ244,[$__,$__2,$lvl,$wp]);
          var $__12=
           new _A_($Control.$Monad.$foldM,[$UHC.$Base.$Monad__DCT74__339__0,$__11,$__10,$__9]);
          var $__13=
           new _A_($JCU.$_24okUNQ343,[$_24x]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__12,$__13]);});
$JCU.$_24okUNQ343=
 new _F_(function($_24x,$_24x2)
         {var $__=
           new _A_($UHC.$Base.$packedStringToString,["jcu.hs:209:17: monadic bind"]);
          var $__4=
           new _A_($UHC.$Base.$fail,[$UHC.$Base.$Monad__DCT74__339__0,$__]);
          var $__5=
           _e_($_24x2);
          var $__8=
           new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0,$_24x]);
          var $__9=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$append,[$_24x,$__5[0]]);
          var $__10=
           new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__9,$__8]);
          return $__10;});
$JCU.$__44__561NEW258=
 new _F_(function($node,$status,$__,$__4)
         {var $__5=
           new _A_($UHC.$Base.$packedStringToString,["<ul id=\"proof-tree-view\" class=\"tree\"/>"]);
          var $__6=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$jQuery,[$__5]);
          var $__7=
           new _A_($JCU.$_24okUNQ412,[$node,$status,$__,$__4]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__6,$__7]);});
$JCU.$_24okUNQ412=
 new _F_(function($node,$status,$__,$__4,$_24x)
         {var $__6=
           [$node,$status];
          var $__7=
           new _A_($UHC.$Base.$_3a,[0,$UHC.$Base.$_5b_5d]);
          var $__8=
           new _A_($JCU.$build_27UNQ243,[$__,$__4,$__7,$node,$__6,$UHC.$Base.$False__]);
          var $__9=
           new _A_($JCU.$_24okUNQ422,[$_24x]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__8,$__9]);});
$JCU.$_24okUNQ422=
 new _F_(function($_24x,$_24x2)
         {var $__=
           new _A_($JCU.$__44__572NEW265,[$_24x,$_24x2]);
          var $__4=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$append,[$_24x,$_24x2]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__4,$__]);});
$JCU.$__44__572NEW265=
 new _F_(function($_24x,$_24x2)
         {var $__=
           new _A_($UHC.$Base.$packedStringToString,["input"]);
          var $__4=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$findSelector,[$_24x2,$__]);
          var $__5=
           new _A_($JCU.$_24okUNQ428,[$_24x]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__4,$__5]);});
$JCU.$_24okUNQ428=
 new _F_(function($_24x,$_24x2)
         {var $__=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$mkJThisEventHandler,[$JCU.$fCheckUNQ246]);
          var $__4=
           new _A_($JCU.$_24okUNQ434,[$_24x,$_24x2]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__,$__4]);});
$JCU.$_24okUNQ434=
 new _F_(function($_24x,$_24x2,$_24x3)
         {var $__=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$wrappedJQueryEvent,[$_24x3]);
          var $__5=
           new _A_($JCU.$_24okUNQ442,[$_24x,$_24x2]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__,$__5]);});
$JCU.$_24okUNQ442=
 new _F_(function($_24x,$_24x2,$_24x3)
         {var $__=
           new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0,$_24x]);
          var $__5=
           new _A_($UHC.$Base.$packedStringToString,["blur"]);
          var $__6=
           new _A_($Language.$UHC.$JS.$Types.$toJS,[$Language.$UHC.$JS.$ECMA.$String.$ToJS__DCT40__2__0,$__5]);
          var $__7=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$__bind,[$_24x2,$__6,$_24x3]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__7,$__]);});
$JCU.$__44__157NEW68=
 new _F_(function($p)
         {var $__=
           new _A_($JCU.$checkProof,[$p]);
          var $__3=
           new _A_($JCU.$_24okUNQ205,[$p]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__,$__3]);});
$JCU.$_24okUNQ205=
 new _F_(function($p,$_24x)
         {var $__=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$jQuery,[$JCU.$ruleTreeId]);
          var $__4=
           new _A_($JCU.$_24okUNQ211,[$p,$_24x]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__,$__4]);});
$JCU.$_24okUNQ211=
 new _F_(function($p,$_24x,$_24x3)
         {var $__=
           new _A_($JCU.$buildRuleUl,[$p,$_24x]);
          var $__5=
           new _A_($JCU.$_24okUNQ217,[$p,$_24x3]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__,$__5]);});
$JCU.$_24okUNQ217=
 new _F_(function($p,$_24x,$_24x3)
         {var $__=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$replaceWith,[$_24x,$_24x3]);
          var $__5=
           new _A_($JCU.$doSubst,[$p]);
          var $__6=
           new _A_($UHC.$Base.$packedStringToString,["#btnSubst"]);
          var $__7=
           [$__6,$Language.$UHC.$JS.$JQuery.$JQuery.$Click__,$__5];
          var $__8=
           new _A_($UHC.$Base.$_3a,[$__7,$UHC.$Base.$_5b_5d]);
          var $__9=
           new _A_($JCU.$toggleClue,[$p]);
          var $__10=
           new _A_($UHC.$Base.$packedStringToString,["#btnCheck"]);
          var $__11=
           [$__10,$Language.$UHC.$JS.$JQuery.$JQuery.$Click__,$__9];
          var $__12=
           new _A_($UHC.$Base.$_3a,[$__11,$__8]);
          var $__13=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$registerEvents,[$__12]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__13,$__]);});
$JCU.$_24okUNQ451=
 new _F_(function($p,$_24x)
         {var $__=
           new _A_($UHC.$Base.$packedStringToString,["#txtSubstFor"]);
          var $__4=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$jQuery,[$__]);
          var $__5=
           new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__4,$Language.$UHC.$JS.$JQuery.$JQuery.$valString]);
          var $__6=
           new _A_($JCU.$_24okUNQ459,[$p,$_24x]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__5,$__6]);});
$JCU.$_24okUNQ459=
 new _F_(function($p,$_24x,$_24x3)
         {var $__=
           new _A_($Models.$tryParseTerm,[$_24x]);
          var $__5=
           _e_($__);
          var $__swJSW555__0;
          switch($__5._tag_)
           {case 0:
             var $__7=
              [$_24x3,$__5._1];
             var $__8=
              new _A_($UHC.$Base.$_3a,[$__7,$UHC.$Base.$_5b_5d]);
             var $__9=
              new _A_($Data.$Map.$fromList,[$__8]);
             var $__10=
              new _A_($UHC.$Base.$_24,[$Language.$Prolog.$NanoProlog.$NanoProlog.$Env__,$__9]);
             var $newP=
              new _A_($Language.$Prolog.$NanoProlog.$NanoProlog.$subst,[$Prolog.$Subst__DCT28__3__0,$__10,$p]);
             var $__12=
              new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0,$UHC.$Base.$True__]);
             var $__13=
              new _A_($JCU.$replaceRuleTree,[$newP]);
             $__swJSW555__0=
              new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__13,$__12]);
             break;
            case 1:
             var $__14=
              new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0,$UHC.$Base.$False__]);
             $__swJSW555__0=
              $__14;
             break;}
          return $__swJSW555__0;});
$JCU.$buildRuleUl=
 new _F_(function($node,$status)
         {var $__=
           new _A_($Data.$Tree.$__40__0__0,[$Language.$Prolog.$NanoProlog.$NanoProlog.$Show__DCT52__14__0]);
          var $__4=
           new _A_($UHC.$Base.$Show__DCT74__87__0,[$UHC.$Base.$Show__DCT74__128__0]);
          var $__5=
           new _A_($JCU.$__44__561NEW258,[$node,$status,$__4,$__]);
          var $__6=
           new _A_($UHC.$Base.$show,[$JCU.$__42__4079__2__0,$status]);
          var $__7=
           new _A_($Debug.$consoleLog,[$__6]);
          var $__8=
           new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__7,$__5]);
          var $__9=
           new _A_($UHC.$Base.$packedStringToString,["buildRuleUl"]);
          var $__10=
           new _A_($Debug.$consoleLog,[$__9]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__10,$__8]);});
$JCU.$replaceRuleTree=
 new _F_(function($p)
         {var $__=
           new _A_($JCU.$__44__157NEW68,[$p]);
          var $__3=
           new _A_($UHC.$Base.$packedStringToString,["replaceRuleTree"]);
          var $__4=
           new _A_($Debug.$consoleLog,[$__3]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__4,$__]);});
$JCU.$doSubst=
 new _F_(function($p,$__)
         {var $__3=
           new _A_($UHC.$Base.$packedStringToString,["#txtSubstSub"]);
          var $__4=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$jQuery,[$__3]);
          var $__5=
           new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__4,$Language.$UHC.$JS.$JQuery.$JQuery.$valString]);
          var $__6=
           new _A_($JCU.$_24okUNQ451,[$p]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__5,$__6]);});
$JCU.$toggleClue=
 new _F_(function($p,$__)
         {var $__3=
           new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0,$UHC.$Base.$True__]);
          var $__4=
           new _A_($JCU.$replaceRuleTree,[$p]);
          var $__5=
           new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__4,$__3]);
          var $__6=
           new _A_($Data.$LocalStorage.$modifyLocalStorage,[$UHC.$Base.$__74__51__0,$UHC.$Base.$__74__50__0,$JCU.$checkProofStoreKey,$UHC.$Base.$not]);
          var $__7=
           new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__6,$__5]);
          var $__8=
           new _A_($UHC.$Base.$packedStringToString,["noClue"]);
          var $__9=
           new _A_($UHC.$Base.$packedStringToString,["#proof-tree-div"]);
          var $__10=
           new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$toggleClassString,[$__9,$__8]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$__10,$__7]);});
$JCU.$_24okUNQ646=
 new _F_(function($status,$_24x)
         {var $__=
           new _A_($JCU.$buildRuleUl,[$JCU.$emptyProof,$status]);
          var $__4=
           new _A_($JCU.$_24okUNQ652,[$_24x]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__,$__4]);});
$Data.$Tree.$Node__=
 new _F_(function($x1,$x2)
         {return {_tag_:0,rootLabel:$x1,subForest:$x2};});
$Prolog.$Correct__=
 new _A_(new _F_(function()
                 {return {_tag_:0};}),[]);
$JCU.$addRuleTree=
 new _A_(new _F_(function()
                 {var $status=
                   new _A_($Data.$Tree.$Node__,[$Prolog.$Correct__,$UHC.$Base.$_5b_5d]);
                  var $__=
                   new _A_($UHC.$Base.$packedStringToString,["#proof-tree-div"]);
                  var $__3=
                   new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$jQuery,[$__]);
                  var $__4=
                   new _A_($JCU.$_24okUNQ646,[$status]);
                  return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__3,$__4]);}),[]);
$JCU.$_24okUNQ671=
 new _F_(function($_24x)
         {var $__=
           new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$JCU.$addExampleGoals,$JCU.$__44__1142]);
          var $__3=
           new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$JCU.$addRules,$__]);
          return new _A_($UHC.$Base.$_3e_3e,[$UHC.$Base.$Monad__DCT74__339__0,$JCU.$addRuleTree,$__3]);});
$Language.$UHC.$JS.$JQuery.$JQuery.$__jQuery=
 new _F_(function($__,$__2)
         {var $__3=
           _e_($__);
          var $__4=
           _e_(jQuery($__3));
          return [$__2,$__4];});
$Language.$UHC.$JS.$Types.$ToJS__CLS28__3__0=
 new _F_(function($ToJS__)
         {var $ToJS__2=
           {_tag_:0,_1:$UHC.$Base.$undefined};
          return $ToJS__2;});
$Language.$UHC.$JS.$ECMA.$String.$stringToJSString=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return primStringToPackedString($__2);});
$Language.$UHC.$JS.$ECMA.$String.$ToJS__NEW81UNQ152EVLDCT40__2__0RDC=
 new _F_(function($ToJS__)
         {var $ToJS__2=
           _e_(new _A_($Language.$UHC.$JS.$Types.$ToJS__CLS28__3__0,[$ToJS__]));
          var $__4=
           {_tag_:0,_1:$Language.$UHC.$JS.$ECMA.$String.$stringToJSString};
          return $__4;});
$Language.$UHC.$JS.$ECMA.$String.$ToJS__NEW79UNQ151DCT40__2__0RDC=
 new _F_(function($ToJS__)
         {var $ToJS__2=
           new _A_($Language.$UHC.$JS.$ECMA.$String.$ToJS__NEW81UNQ152EVLDCT40__2__0RDC,[$ToJS__]);
          return $ToJS__2;});
$Language.$UHC.$JS.$ECMA.$String.$ToJS__UNQ151DCT40__2__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($Language.$UHC.$JS.$ECMA.$String.$ToJS__NEW79UNQ151DCT40__2__0RDC,[$Language.$UHC.$JS.$ECMA.$String.$ToJS__UNQ151DCT40__2__0RDC]);}),[]);
$Language.$UHC.$JS.$ECMA.$String.$ToJS__DCT40__2__0=
 new _A_(new _F_(function()
                 {return $Language.$UHC.$JS.$ECMA.$String.$ToJS__UNQ151DCT40__2__0RDC;}),[]);
$Language.$UHC.$JS.$Types.$toJS=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._1;});
$Language.$UHC.$JS.$JQuery.$JQuery.$__128__1120=
 new _A_(new _F_(function()
                 {return new _A_($Language.$UHC.$JS.$Types.$toJS,[$Language.$UHC.$JS.$ECMA.$String.$ToJS__DCT40__2__0]);}),[]);
$Language.$UHC.$JS.$JQuery.$JQuery.$jQuery=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_2e,[$Language.$UHC.$JS.$JQuery.$JQuery.$__jQuery,$Language.$UHC.$JS.$JQuery.$JQuery.$__128__1120]);}),[]);
$JCU.$initProofTree=
 new _A_(new _F_(function()
                 {var $__=
                   new _A_($UHC.$Base.$packedStringToString,["#mainLeft"]);
                  var $__2=
                   new _A_($Language.$UHC.$JS.$JQuery.$JQuery.$jQuery,[$__]);
                  return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__2,$JCU.$_24okUNQ671]);}),[]);
$JCU.$_24okUNQ741=
 new _F_(function($_24x)
         {var $__=
           new _A_($Language.$UHC.$JS.$Prelude.$wrapIO,[$JCU.$initProofTree]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$__,$JCU.$_24okUNQ747]);});
$UHC.$Base.$Functor__CLS74__44__0=
 new _F_(function($Functor__)
         {var $Functor__2=
           {_tag_:0,_1:$UHC.$Base.$undefined};
          return $Functor__2;});
$UHC.$Base.$return=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._4;});
$UHC.$Base.$_2e=
 new _F_(function($f,$g,$x)
         {var $__=
           new _A_($g,[$x]);
          return new _A_($f,[$__]);});
$UHC.$Base.$primbindIO=
 new _F_(function($__,$f,$w)
         {var $__4=
           new _A_($__,[$w]);
          var $__5=
           _e_($__4);
          var $w_278=
           _e_($__5[0]);
          var $__9=
           new _A_($f,[$__5[1]]);
          return new _A_($__9,[$w_278]);});
$UHC.$Base.$__78__7648__0=
 new _F_(function($q,$__)
         {return $q;});
$UHC.$Base.$Monad__CLS74__45__0DFLUHC_2eBase_2e_3e_3e=
 new _F_(function($Monad__,$p,$q)
         {var $__=
           new _A_($UHC.$Base.$__78__7648__0,[$q]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$Monad__,$p,$__]);});
$UHC.$Base.$Monad__CLS74__45__0=
 new _F_(function($Monad__)
         {var $__=
           new _A_($UHC.$Base.$Monad__CLS74__45__0DFLUHC_2eBase_2e_3e_3e,[$Monad__]);
          var $Monad__3=
           {_tag_:0,_1:$__,_2:$UHC.$Base.$undefined,_3:$UHC.$Base.$error,_4:$UHC.$Base.$undefined};
          return $Monad__3;});
$UHC.$Base.$primretIO=
 new _F_(function($x,$w)
         {return [$w,$x];});
$UHC.$Base.$Monad__NEW3761UNQ10224EVLDCT74__339__0RDC=
 new _F_(function($Monad__)
         {var $Monad__2=
           _e_(new _A_($UHC.$Base.$Monad__CLS74__45__0,[$Monad__]));
          var $__7=
           {_tag_:0,_1:$Monad__2._1,_2:$UHC.$Base.$primbindIO,_3:$Monad__2._3,_4:$UHC.$Base.$primretIO};
          return $__7;});
$UHC.$Base.$Monad__NEW3759UNQ10223DCT74__339__0RDC=
 new _F_(function($Monad__)
         {var $Monad__2=
           new _A_($UHC.$Base.$Monad__NEW3761UNQ10224EVLDCT74__339__0RDC,[$Monad__]);
          return $Monad__2;});
$UHC.$Base.$Monad__UNQ10223DCT74__339__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Monad__NEW3759UNQ10223DCT74__339__0RDC,[$UHC.$Base.$Monad__UNQ10223DCT74__339__0RDC]);}),[]);
$UHC.$Base.$Monad__DCT74__339__0=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$Monad__UNQ10223DCT74__339__0RDC;}),[]);
$UHC.$Base.$_3e_3e_3d=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._2;});
$UHC.$Base.$Functor__DCT74__338__0DFLUHC_2eBase_2efmap=
 new _F_(function($f,$x)
         {var $__=
           new _A_($UHC.$Base.$return,[$UHC.$Base.$Monad__DCT74__339__0]);
          var $__4=
           new _A_($UHC.$Base.$_2e,[$__,$f]);
          return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$x,$__4]);});
$UHC.$Base.$Functor__NEW3771UNQ10285EVLDCT74__338__0RDC=
 new _F_(function($Functor__)
         {var $Functor__2=
           _e_(new _A_($UHC.$Base.$Functor__CLS74__44__0,[$Functor__]));
          var $__4=
           {_tag_:0,_1:$UHC.$Base.$Functor__DCT74__338__0DFLUHC_2eBase_2efmap};
          return $__4;});
$UHC.$Base.$Functor__NEW3769UNQ10282DCT74__338__0RDC=
 new _F_(function($Functor__)
         {var $Functor__2=
           new _A_($UHC.$Base.$Functor__NEW3771UNQ10285EVLDCT74__338__0RDC,[$Functor__]);
          return $Functor__2;});
$UHC.$Base.$Functor__UNQ10282DCT74__338__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$Functor__NEW3769UNQ10282DCT74__338__0RDC,[$UHC.$Base.$Functor__UNQ10282DCT74__338__0RDC]);}),[]);
$UHC.$Base.$Functor__DCT74__338__0=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$Functor__UNQ10282DCT74__338__0RDC;}),[]);
$UHC.$Base.$fmap=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._1;});
$Language.$UHC.$JS.$W3C.$HTML5.$__pathName=
 new _F_(function($__)
         {var $__2=
           _e_(window.location.pathname);
          return [$__,$__2];});
$Language.$UHC.$JS.$Types.$fromJS=
 new _F_(function($x)
         {var $x2=
           _e_($x);
          return $x2._1;});
$Language.$UHC.$JS.$ECMA.$String.$jsStringToString=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$packedStringToString;}),[]);
$Language.$UHC.$JS.$Types.$FromJS__CLS28__4__0=
 new _F_(function($FromJS__)
         {var $FromJS__2=
           {_tag_:0,_1:$UHC.$Base.$undefined};
          return $FromJS__2;});
$UHC.$Base.$_5b_5d=
 new _A_(new _F_(function()
                 {return {_tag_:1};}),[]);
$UHC.$Base.$_3a=
 new _F_(function($x1,$x2)
         {return {_tag_:0,_1:$x1,_2:$x2};});
$UHC.$Base.$packedStringNull=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return primPackedStringNull($__2);});
$UHC.$Base.$packedStringTail=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return primPackedStringTail($__2);});
$UHC.$Base.$packedStringHead=
 new _F_(function($__)
         {var $__2=
           _e_($__);
          return primPackedStringHead($__2);});
$UHC.$Base.$primThrowException=
 new _F_(function($__)
         {return primThrowException($__);});
$UHC.$Base.$throw=
 new _A_(new _F_(function()
                 {return $UHC.$Base.$primThrowException;}),[]);
$UHC.$Base.$ErrorCall__=
 new _F_(function($x1)
         {return {_tag_:6,_1:$x1};});
$UHC.$Base.$error=
 new _F_(function($s)
         {var $__=
           new _A_($UHC.$Base.$ErrorCall__,[$s]);
          return new _A_($UHC.$Base.$throw,[$__]);});
$UHC.$Base.$__78__1373=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$packedStringToString,["Prelude.undefined"]);}),[]);
$UHC.$Base.$undefined=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$error,[$UHC.$Base.$__78__1373]);}),[]);
$UHC.$Base.$packedStringToString=
 new _F_(function($p)
         {var $__=
           new _A_($UHC.$Base.$packedStringNull,[$p]);
          var $__3=
           _e_($__);
          var $__swJSW565__0;
          switch($__3._tag_)
           {case 0:
             var $__4=
              new _A_($UHC.$Base.$packedStringTail,[$p]);
             var $__5=
              new _A_($UHC.$Base.$packedStringToString,[$__4]);
             var $__6=
              new _A_($UHC.$Base.$packedStringHead,[$p]);
             var $__7=
              new _A_($UHC.$Base.$_3a,[$__6,$__5]);
             $__swJSW565__0=
              $__7;
             break;
            case 1:
             $__swJSW565__0=
              $UHC.$Base.$_5b_5d;
             break;}
          return $__swJSW565__0;});
$Language.$UHC.$JS.$ECMA.$String.$FromJS__NEW102UNQ162EVLDCT40__4__0RDC=
 new _F_(function($FromJS__)
         {var $FromJS__2=
           _e_(new _A_($Language.$UHC.$JS.$Types.$FromJS__CLS28__4__0,[$FromJS__]));
          var $__4=
           {_tag_:0,_1:$Language.$UHC.$JS.$ECMA.$String.$jsStringToString};
          return $__4;});
$Language.$UHC.$JS.$ECMA.$String.$FromJS__NEW100UNQ161DCT40__4__0RDC=
 new _F_(function($FromJS__)
         {var $FromJS__2=
           new _A_($Language.$UHC.$JS.$ECMA.$String.$FromJS__NEW102UNQ162EVLDCT40__4__0RDC,[$FromJS__]);
          return $FromJS__2;});
$Language.$UHC.$JS.$ECMA.$String.$FromJS__UNQ161DCT40__4__0RDC=
 new _A_(new _F_(function()
                 {return new _A_($Language.$UHC.$JS.$ECMA.$String.$FromJS__NEW100UNQ161DCT40__4__0RDC,[$Language.$UHC.$JS.$ECMA.$String.$FromJS__UNQ161DCT40__4__0RDC]);}),[]);
$Language.$UHC.$JS.$ECMA.$String.$FromJS__DCT40__4__0=
 new _A_(new _F_(function()
                 {return $Language.$UHC.$JS.$ECMA.$String.$FromJS__UNQ161DCT40__4__0RDC;}),[]);
$Language.$UHC.$JS.$W3C.$HTML5.$__122__593=
 new _A_(new _F_(function()
                 {return new _A_($Language.$UHC.$JS.$Types.$fromJS,[$Language.$UHC.$JS.$ECMA.$String.$FromJS__DCT40__4__0]);}),[]);
$Language.$UHC.$JS.$W3C.$HTML5.$pathName=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$fmap,[$UHC.$Base.$Functor__DCT74__338__0,$Language.$UHC.$JS.$W3C.$HTML5.$__122__593,$Language.$UHC.$JS.$W3C.$HTML5.$__pathName]);}),[]);
$JCU.$main=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Base.$_3e_3e_3d,[$UHC.$Base.$Monad__DCT74__339__0,$Language.$UHC.$JS.$W3C.$HTML5.$pathName,$JCU.$_24okUNQ741]);}),[]);
var $main=
 new _A_(new _F_(function()
                 {return new _A_($UHC.$Run.$ehcRunMain,[$JCU.$main]);}),[]);
_e_(new _A_($main,[[]]));
