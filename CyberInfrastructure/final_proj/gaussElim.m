function [Ab, xs] = gaussElim(A, b)

Ab = [A, b];

n = size(A, 1);

for i = 1:n;
    %Scale row
    Ab(i, :) = Ab(i, :) ./ Ab(i, i);
    
    for j = i+1:n
        pivot = Ab(j, i) / Ab(i, i);
        Ab(j, :) = pivot * Ab(i, :) - Ab(j, :);
    end
end

%Solve for x
xs = zeros(n, 1);
for i = n:-1:1
    bi = Ab(i, end);
    for j = n:-1:i+1
        bi = bi - Ab(i, j) * xs(j);
    end
    xs(i) = bi;
end



