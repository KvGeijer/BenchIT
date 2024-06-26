/********************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id: simple.c 1 2009-09-11 12:26:19Z william $
 * $URL: svn+ssh://william@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/kernel/sort/bubblesort/C/0/0/float/simple.c $
 * For license details see COPYING in the package base directory
 *******************************************************************/

#include "simple.h"
#include "interface.h"

double simple(myinttype * pi_prob_size)
{
  double dresult = 1.0;
  myinttype ii = 0, pre = 0, prepre = 0;
  

  switch (* pi_prob_size)
  {
    case 0:
            break;
    case 1:
            break;
    default:
            pre = *pi_prob_size - 1;
            prepre = pre - 1;
            dresult = (double) (simple(&pre) + simple(&prepre));
  }

              
/*  for (ii=*pi_prob_size; ii>0; ii--)
  {
    dresult = dresult * ii;
    dresult = sqrt(dresult);
  }
*/
  return dresult;
}


void bubblesortf(float *pfsort, long lnumber)
   {
   int  ii, ij;
   float fh;

   /*initialize variables*/
   fh = 0;
   ii = 0;
   ij = 0;

   /*moves "biggest" element in the rest array
     to the correct position by... */
   for (ii = (lnumber - 1); ii >= 0; ii--)
      {
      /*changing neighbours until the position is set */
      for (ij = 1; ij <= ii; ij++)
         {
         /*if neighbouring objects are wrong way around ... */
         if (pfsort[ij - 1] > pfsort[ij])
            {
            /*change them */
            fh = pfsort[ij - 1];
            pfsort[ij - 1] = pfsort[ij];
            pfsort[ij] = fh;
            }
         }
      }
   }


int verifyf(float *pfprobe, long lelements)
   {
   int ii;

   /*initialize variables*/
   ii = 0;

/*any element on position n+1 has to be larger
  or equal to element on position n...*/
   for (ii = 1; ii < lelements; ii++)
      {
      if (pfprobe[ii - 1] > pfprobe[ii])
         {
         return 0;
         }
      }

   /*"1" means success */
   return 1;
   }

