function [L] = luDecomp(A)

%l11 = sqrt(a11)
%lj1 = aj1/l11, j > 1
%lji = 1/lii(aji - sum(ljk * lik)), j > i > 1    (k = 1 to i-1)
%lii = sqrt(aii - sum(lik^2)), i < i < n (k = 1 to i-1) 
 
L = zeros(size(A));
n = size(A, 1);
for j = 1:n
    for i = j:n
        L(j, j) = sqrt(A(j, j) - sum(L(j, 1:j-1).^2));
        L(i, j) = 1/L(j, j) * (A(i, j) - sum(L(i, 1:j-1) .* L(j, 1:j-1)));
    end
end


end