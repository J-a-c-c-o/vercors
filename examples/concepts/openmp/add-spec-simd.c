// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: case OpenMPaddSimd
// suite puptol
// tools silicon

/*
 * Trivial for-simd example.
 *
 */
#include <omp.h>
#include <stdio.h>

/*@
  context_everywhere len > 0 && (len % 4 == 0) && a != NULL && b != NULL && c !=
NULL; context \pointer(a, len, 1\2) ** \pointer(b, len, 1\2) ** \pointer(c, len,
1\2); ensures (\forall int k = 0 .. len; c[k]==a[k]+b[k]);
@*/
void add(int len, int a[], int b[], int c[]) {
#pragma omp parallel
  {
/*@
  context (\forall* int k;0 <= k && k < len ; Perm(a[k],1\2));
  context (\forall* int k;0 <= k && k < len ; Perm(b[k],1\2));
  context (\forall* int k;0 <= k && k < len ; Perm(c[k],1));
  ensures (\forall  int k;0 <= k && k < len ; c[k]==a[k]+b[k]);
@*/
#pragma omp for simd schedule(static) simdlen(4)
    for (int i = 0; i < len; i++)
    /*@
      context Perm(c[i],1) ** Perm(b[i],1\2) ** Perm(a[i],1\2);
      ensures c[i] == a[i] + b[i];
    @*/
    {
      c[i] = a[i] + b[i];
    }
  }
}