#include "fol.hpp"
#include "unionFind.hpp"
#include <vector>
#include <set>
#include <map>
using namespace std;
extern int yyparse();

extern Formula parsed_formula;
extern vector<Formula>* parsed_set_of_formulas;

void getTermsFromTerm(FunctionTerm *ft, TermSet& allTerms){ 
   Term t = make_shared<FunctionTerm>(ft->getSymbol(),ft->getOperands());
   allTerms.insert(t);
   if(ft->getOperands().size()==0){
      return ;
   }
   for(auto i:ft->getOperands())
   {
      FunctionTerm* temp = (FunctionTerm*)i.get();
      getTermsFromTerm(temp,allTerms);
   }

}

void getTermsFromFormula(Formula f,  TermSet& allTerms ){
   Equality *atom = (Equality*)f.get();
   FunctionTerm* ft1 = (FunctionTerm*)atom->getLeftOperand().get();
   getTermsFromTerm(ft1,allTerms);
   FunctionTerm* ft2 = (FunctionTerm*)atom->getRightOperand().get();
   getTermsFromTerm(ft2,allTerms);
}

void getTerms(vector<Formula>* vf, Formula f, TermSet& allTerms){
   for(auto i: *vf)
      getTermsFromFormula(i,allTerms);
   getTermsFromFormula(f,allTerms);
}

void getUseMap(UseMap &um, TermSet &t){
   for(auto i: t){
      TermSet temp;
      //prolazimo kroz termove da vidimo da li je deo nekog terma
      for(auto j: t){
      FunctionTerm* f = (FunctionTerm*)j.get();
      const vector<Term> &terms = f->getOperands();
      for(unsigned k=0;k<terms.size();k++){    
         if(i->equalTo(terms[k]))
            temp.insert(j);
      }
      }
      um.insert(make_pair(i,temp));
   }
}

void printUseMap(UseMap &um){
   for(auto i:um){
      cout << i.first <<" : ";
      for(auto v:i.second)
         cout << v << " ";
      cout<<endl;
   }
   cout<<endl;
}

bool cong(Term firstTerm, Term secondTerm, UnionFind &u){
   
   FunctionTerm* f = (FunctionTerm*)firstTerm.get();
   FunctionTerm* g = (FunctionTerm*)secondTerm.get();
   
   if(f->getSymbol()!=g->getSymbol())
      return false;
   
   const vector<Term> &terms1 = f->getOperands();
   const vector<Term> &terms2 = g->getOperands();

   for(unsigned i=0; i<terms1.size(); i++){
      if(u.findRootOfTerm(terms1[i]) != u.findRootOfTerm(terms2[i]))
         return false;
   }
   return true;
}

//izracunava T_s = U { use(s') | find(s') == find(s) }
TermSet getSetsForMerge(Term s, UnionFind &u){
   UseMap& um = u.getUMap();
   TermSet equivalencySet = u.findTermsFromTheSameSet(s);
   TermSet returnValue;

   TermSet use = um[s]; 
   for(auto term: use){
      returnValue.insert(term);
   }
   for(auto t: equivalencySet){
      TermSet use = um[t];
      for(auto term: use){
         returnValue.insert(term);
      }
   }
   return returnValue;
}

void merge(Term s, Term t, UnionFind &u){
   TermSet firstSet = getSetsForMerge(s,u);
   TermSet secondSet = getSetsForMerge(t,u);
   u.unionOfSets(s,t);
   for(auto a: firstSet){
      for(auto b: secondSet){
         if(u.findRootOfTerm(a)!=u.findRootOfTerm(b) && cong(a,b,u)){
            merge(a,b,u);
         }
      }
   }
}

void cc(vector<Formula>* E, TermSet T, UnionFind &u){
   for(auto f: *E){
      Equality *atom = (Equality*)f.get();
      const Term &s = atom->getLeftOperand();
      const Term &t = atom->getRightOperand();
      int root1 = u.findRootOfTerm(s);
      int root2 = u.findRootOfTerm(t);
      if(root1!=root2){
         merge(s,t,u);
      }
   }
}

bool checkEquality(vector<Formula>* E, Formula f){
   TermSet allTerms;
   getTerms(E, f, allTerms);
   UseMap um;
   getUseMap(um,allTerms);
   UnionFind u(allTerms, um);
   cc(E, allTerms, u);
   cout << "-----Skup termova-----"<<endl;
   for(auto i:allTerms)
      cout << i <<" ";
   cout<<endl;
   cout << "-----Use mapa-----"<<endl;
   printUseMap(um);
   //da li termovi iz f pripadaju istoj klasi ekvivalencije
   Equality *atom = (Equality*)f.get();
   const Term& ft1 = atom->getLeftOperand();
   const Term& ft2 = atom->getRightOperand();
   cout<< "-----Klase ekvivalencije-----" << endl;
   u.printUnionFind(); 
   cout << "------------------------------" << endl;
   TermSet roots = u.findAllRoots();
   for(auto term: roots){
      TermSet classEquivalency = u.findTermsFromTheSameSet(term);
      if(classEquivalency.find(ft1)!=classEquivalency.end() || term==ft1){
         if(classEquivalency.find(ft2)!=classEquivalency.end() || term==ft2){
            return true;
         }
      }
   }
   return false;
}

int main()
{
   yyparse();

   if(checkEquality(parsed_set_of_formulas,parsed_formula))
      cout << "Termovi iz formule " << parsed_formula << " se nalaze u istim klasama ekvivalencije!"  << endl;
   else
      cout << "Termovi iz formule " << parsed_formula << " se  ne nalaze u istim klasama ekvivalencije!" << endl;
   
   return 0;
}
