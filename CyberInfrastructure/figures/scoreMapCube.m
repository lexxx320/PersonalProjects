[x, y, z] = meshgrid(-2:2.2, -2:.25:2, -2:.16:2);

v = x.* exp(-x.^2-z.^2);

xslice = [-2, 2];
yslice = [-2, 2];
zslice = [-2, 2];
slice(x, y,z,v,xslice, yslice, zslice);
colormap colorcube

%% 
d = 4;
[x, y, z] = meshgrid(0:d, 0:d, 0:d);

d2 = d + 1;
v = ones(d2, d2, d2);


count = 1;

for i = 1:d2
    for j = d2:-1:1
        for k = d2:-1:1
            v(i, j, k) = count;
            disp([i, j, k]);
        end
        count = count+1;
    end
end


xslice = [0, d];
yslice = [0, d];
zslice = [0, d];
slice(x, y,z,v,xslice, yslice, zslice);
colormap jet

