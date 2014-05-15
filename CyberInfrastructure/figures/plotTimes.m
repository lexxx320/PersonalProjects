
count = 1;
for i = 1:3:length(times)
    meanTimes(count) = mean(times(i:i+2));
    count = count+1;
end


t = [times1(1:3); meanTimes'];