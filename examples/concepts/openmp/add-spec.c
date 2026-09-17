// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: case OpenMPadd
//:: suite puptol
//:: tools silicon
/*
 * Demonstrates how two loops that must be fused to be
 * data race free can be specified and verified.
 */
#include <omp.h>
#include <stdio.h>

/*@
  context \pointer(a, len, 1\2) ** \pointer(b, len, 1\2) ** \pointer(c, len,
write); ensures   (\forall  int k;0 <= k && k < len ; c[k]==a[k]+b[k]);
@*/
void add(int len, int a[], int b[], int c[]) {
#pragma omp parallel
  {
    /*@
      context \pointer(a, len, 1\2) ** \pointer(b, len, 1\2) ** \pointer(c,
    len, write); ensures (\forall  int k;0 <= k && k < len ;
    c[k]==a[k]+b[k]);
    @*/

#pragma omp for schedule(static)
    for (int i = 0; i < len; i++)
    /*@
      context a != NULL && c != NULL;
      context Perm(c[i],1) ** Perm(a[i],1\2);
      ensures c[i] == a[i];
    @*/
    {
      c[i] = a[i];
    }
#pragma omp for schedule(static)
    for (int i = 0; i < len; i++)
    /*@
      context b != NULL && c != NULL && a != NULL;
      context Perm(c[i],1) ** Perm(b[i],1\2) ** Perm(a[i],1\2);
      requires c[i] == a[i];
      ensures c[i] == a[i] + b[i];
    @*/
    {
      c[i] = c[i] + b[i];
    }
  }
}
