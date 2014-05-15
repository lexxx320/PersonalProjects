if ~exist('ssh', 'var')
    load /project/expeditions/eddies_project_data/ssh_data/data/global_ssh_1992_2011_with_nan.mat
end
addpath('/project/expeditions/lem/eddy_repo/code/luke/chelton_algorithm/');
load /project/expeditions/eddies_project_data/results/global_results/oct7/cyclonic/cyclonic_19921014.mat


sshT1 = ssh(:, :, 1);



[x, y] = ind2sub(size(sshT1), eddies(12).Stats.PixelIdxList);
    
block = sshT1(min(x) - 2:max(x)+2, min(y)-2:max(y)+2);
surf(block);

hold on
C = zeros(size(block));
C(:, :, 1:3) = 0;
surf(zeros(size(block)) + 11, C);

%% 
block2 = repmat(block, [1, 1, 3]);
C2 = zeros(size(block2));

%Below Thresh
temp = zeros(size(block));
temp(floor(block) < 11) = 1;
C2(:, :, 3) = temp;

%Above Thresh
temp = ~temp;
C2(:, :, 1) = temp;
surf(block, C2);
hold on 
surf(zeros(size(block)) + 11, zeros(size(block, 1), size(block, 2), 3));