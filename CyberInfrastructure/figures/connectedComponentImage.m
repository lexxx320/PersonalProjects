d = 5;
[x, y, z] = meshgrid(0:d, 0:d, 0:d);

d2 = d + 1;
v = ones(d2, d2, d2);

for i = d2:-1:1
    for j = d2:-1:1
        for k = d2:-1:1
            v(j, k, i) = k;
        end
    end
end

v(:, end, :) = v(:, end-1, :);

xslice = [0, d];
yslice = [0, d];
zslice = [0, d];
slice(x, y,z,v,xslice, yslice, zslice);
colormap jet

view(-70, 10);
colorbar;
