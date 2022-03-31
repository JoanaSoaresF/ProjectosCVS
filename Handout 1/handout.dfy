/**
CVS 2021-22 Handout 1
Realizado por:
Gonçalo Martins Lourenço nº55780
Joana Soares Faria  nº55754
 */

method peasantMult(a: int, b: int) returns (r: int)
    requires b > 0
    ensures r == a * b
    {
        //TODO
    }


method euclidianDiv(a: int,b : int) returns (q: int,r: int)
    requires a >= 0 // é só para fazer para positivos?
    requires b > 0
    ensures q == a / b
    ensures r == a % b
    {
        //TODO

    }