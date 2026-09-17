// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: case OpenMPcopy
//:: tools silicon

/*
 * Array copy using parallel for loop in OpenMP.
 */

#include <omp.h>
#include <stdio.h>

/*@
  context \pointer(a, len, write) ** \pointer(b, len, 1\2);
  ensures   (\forall  int k;0 <= k && k < len ; a[k]==b[k]);
  ensures   (\forall  int k;0 <= k && k < len ; b[k]==\old(b[k]));
@*/
void copy(int len, int a[], int b[]) {
  int i;
#pragma omp parallel for private(i)
  for (i = 0; i < len; i++)
  /*@
    context a != NULL && b != NULL;
    context Perm(a[i],1) ** Perm(b[i],1\4);
    ensures a[i] == b[i];
  @*/
  {
    a[i] = b[i];
  }
}
