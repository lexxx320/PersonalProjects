function [mid] = bisection(f, tol, a, b) 

mid = (b-a)/2;

while(mid >= tol)
    fMid = f(a + mid);
    if(fMid * f(a) >= 0) %Same sign
        a = a+mid;
    else
        b = a+mid;
    end
    
    mid = (b-a)/2;
end

mid = a+mid;

end