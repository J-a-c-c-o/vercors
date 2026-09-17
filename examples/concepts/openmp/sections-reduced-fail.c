// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: case OpenMPSectionReducedFail1
//:: tools silicon
//:: verdict Fail
/*
 * Demonstrates how two loops that must be fused to be
 * data race free can be specified and verified.
 */
#include <omp.h>
#include <stdio.h>

/*@
  context \pointer(a, len, 1\2) ** \pointer(b, len, 1\2);
  context \pointer(c, len, write) ** \pointer(d, len, write);
  ensures   (\forall  int k;0 <= k && k < len ; c[k]==a[k]+b[k]);
  ensures   (\forall  int k;0 <= k && k < len ; d[k]==a[k]*b[k]);
@*/
void addmul(int len, int a[], int b[], int c[], int d[]) {
#pragma omp parallel
  {
    /*@
      context \pointer(a, len, 1\2) ** \pointer(b, len, 1\2);
      context \pointer(c, len, write) ** \pointer(d, len, write);
      ensures   (\forall  int k;0 <= k && k < len ; c[k]==a[k]+b[k]);
      ensures   (\forall  int k;0 <= k && k < len ; d[k]==a[k]*b[k]);
    @*/

#pragma omp sections
    {
#pragma omp section
      {
#pragma omp for schedule(static) nowait
        for (int i = 0; i < len; i++)
        /*@
          context a != NULL && c != NULL;
          context Perm(c[i],1) ** Perm(a[i],1\4);
          ensures c[i] == a[i];
        @*/
        {
          c[i] = a[i];
        }
#pragma omp for schedule(static)
        for (int i = 0; i < len; i++)
        /*@
          context b != NULL && c != NULL;
          context Perm(c[i],1) ** Perm(b[i],1\4);
          ensures c[i] == \old(c[i]) + b[i];
        @*/
        {
          c[i] = c[i] + b[i];
        }
      } // section
#pragma omp section
      {
#pragma omp for schedule(static)
        for (int i = 0; i < len; i++)
        /*@
          context a != NULL && d != NULL;
          context Perm(d[i],1) ** Perm(a[i],1\4);
          ensures d[i] == a[i];
        @*/
        {
          d[i] = a[i];
        }
#pragma omp for schedule(static)
        for (int i = 0; i < len; i++)
        /*@
          context b != NULL && d != NULL;
          context Perm(d[i],1) ** Perm(b[i],1);
          ensures d[i] == \old(d[i]) * b[i];
        @*/
        {
          d[i] = d[i] * b[i];
        }
      } // section
    } // sections
  } // parallel
} // method