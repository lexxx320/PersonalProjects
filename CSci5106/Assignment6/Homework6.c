#include <stdlib.h>
#include <stdio.h>

typedef enum tag{
  seqProd, assignProd, addProd, subProd, multProd, divProd, varNameProd, constantProd
}Production;

struct Stmt_t{
  Production production;
  union{
    struct Seq{
      struct Stmt_t *first;
      struct Stmt_t *rest;
    }seq;
    struct Assignment{
      char *lh;
      struct Expr_t *rh;
    }assignment;
  };
};

struct Expr_t{
  Production production;
  union{
    struct Binary{
      struct Expr_t *left;
      struct Expr_t *right;
    } binary;
    int value;
    char *name;
  };
};


struct Expr_t *mkVarRef(char * name){
  struct Expr_t *e = (struct Expr_t*)malloc(sizeof(struct Expr_t));
  e->production = varNameProd;
  e->name = name;
  return e;
}

struct Expr_t *mkInt(int val){
  struct Expr_t *e = (struct Expr_t*)malloc(sizeof(struct Expr_t));
  e->production = constantProd;
  e->value = val;
  return e;
}

struct Expr_t *mkExpr(struct Expr_t *left, struct Expr_t *right, Production prod){
  struct Expr_t *e = (struct Expr_t*)malloc(sizeof(struct Expr_t));
  e->production = prod;
  e->binary.left = left;
  e->binary.right = right;
  return e;
}

struct Stmt_t * mkAssign(char* lh, struct Expr_t *rh){
  struct Stmt_t *assign = (struct Stmt_t*)malloc(sizeof(struct Stmt_t));
  assign->production = assignProd;
  assign->assignment.lh = lh;
  assign->assignment.rh = rh;
  return assign;
}

struct Stmt_t *consStmt(struct Stmt_t *first, struct Stmt_t *rest){
  struct Stmt_t *stmt = (struct Stmt_t*)malloc(sizeof(struct Stmt_t));
  stmt->production = seqProd;
  stmt->seq.first = first;
  stmt->seq.rest = rest;
  return stmt;
}

struct Stmt_t * mkTree(){
  //--------a = 1;-------------
  struct Stmt_t *firstAssignment = mkAssign("a", mkInt(1));
  //--------b = 2;--------------
  struct Stmt_t *secondAssignment = mkAssign("b", mkInt(2));
  //--------c = b+a*3;----------
  struct Stmt_t * thirdAssignment = mkAssign("c", mkExpr(mkVarRef("b"), mkExpr(mkVarRef("a"), mkInt(3), multProd), addProd));
  //--------b = c/2;------------
  struct Stmt_t * fourthAssignment = mkAssign("b", mkExpr(mkVarRef("c"), mkInt(2), divProd));
  //--------a = b*c-3;-----------
  struct Stmt_t *fifthAssignment = mkAssign("a", mkExpr(mkExpr(mkVarRef("b"), mkVarRef("c"), multProd), mkInt(3), subProd));
  return consStmt(firstAssignment, consStmt(secondAssignment, consStmt(thirdAssignment, consStmt(fourthAssignment, fifthAssignment))));
  
}

void translateExpr(struct Expr_t *e, int i){
  switch(e->production){
    case 2: //add production
      translateExpr(e->binary.left, i);
      translateExpr(e->binary.right, i+1);
      printf("AddOp R%d, R%d, R%d\n", i, i, i+1);
      break;
    case 3: //sub production
      translateExpr(e->binary.left, i);
      translateExpr(e->binary.right, i+1);
      printf("SubOp R%d, R%d, R%d\n", i, i, i+1);
      break;
    case 4: //mul production
      translateExpr(e->binary.left, i);
      translateExpr(e->binary.right, i+1);
      printf("MultOp R%d, R%d, R%d\n", i, i, i+1);
      break;
    case 5: //div production
      translateExpr(e->binary.left, i);
      translateExpr(e->binary.right, i+1);
      printf("DivOp R%d, R%d, R%d\n", i, i, i+1);
      break;
    case 6: //varRef production
      printf("Load R%d, %s\n", i, e->name);
      break;
    case 7: //constant production
      printf("LoadC R%d, %d\n", i, e->value);
      break;
    default:
      printf("Expression production not recognized.\n");
  }
}
void translateStmt(struct Stmt_t *s, int i){
  switch(s->production){
    case 0: //seq
      translateStmt(s->seq.first, i);
      translateStmt(s->seq.rest, i);
      break;
    case 1: //assignment
      translateExpr(s->assignment.rh, i);
      printf("store %s, R%d\n", s->assignment.lh, i);
      
      break;
    default:
      printf("Statment production type not recognized.\n");
  }
}
void printExpr(struct Expr_t *e){
  switch(e->production){
    case 2: //add production
      printExpr(e->binary.left);
      printf(" + ");
      printExpr(e->binary.right);
      break;
    case 3: //sub production
      printExpr(e->binary.left);
      printf(" - ");
      printExpr(e->binary.right);
      break;
    case 4: //mul production
      printExpr(e->binary.left);
      printf(" * ");
      printExpr(e->binary.right);
      break;
    case 5: //div production
      printExpr(e->binary.left);
      printf(" / ");
      printExpr(e->binary.right);
      break;
    case 6: //varRef production
      printf("%s", e->name);
      break;
    case 7: //constant production
      printf("%d", e->value);
      break;
    default:
      printf("Expression production not recognized.\n");
  }
}

void printStmt(struct Stmt_t *s){
  switch(s->production){
    case 0: //seq
      printStmt(s->seq.first);
      printStmt(s->seq.rest);
      break;
    case 1: //assignment
      printf("%s = ", s->assignment.lh);
      printExpr(s->assignment.rh);
      printf(";\n");
      break;
    default:
      printf("Statment production type not recognized.\n");
  }
}

int main(int argc, char **argv){
  struct Stmt_t *statements = mkTree();
  printf("unparse: \n");
  printStmt(statements);
  printf("\nTranslation:\n");
  translateStmt(statements, 0);

  return 0;
}



